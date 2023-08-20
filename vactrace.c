/* ******************************************************************************
 * Copyright (c) 2011-2021 Google, Inc.  All rights reserved.
 * Copyright (c) 2010 Massachusetts Institute of Technology  All rights reserved.
 * ******************************************************************************/

 /*
  * Redistribution and use in source and binary forms, with or without
  * modification, are permitted provided that the following conditions are met:
  *
  * * Redistributions of source code must retain the above copyright notice,
  *   this list of conditions and the following disclaimer.
  *
  * * Redistributions in binary form must reproduce the above copyright notice,
  *   this list of conditions and the following disclaimer in the documentation
  *   and/or other materials provided with the distribution.
  *
  * * Neither the name of VMware, Inc. nor the names of its contributors may be
  *   used to endorse or promote products derived from this software without
  *   specific prior written permission.
  *
  * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
  * ARE DISCLAIMED. IN NO EVENT SHALL VMWARE, INC. OR CONTRIBUTORS BE LIABLE
  * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
  * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
  * DAMAGE.
  */

#include <stdio.h>
#include <string.h> /* for memset */
#include <stddef.h> /* for offsetof */
#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "drx.h"
#include "utils.h"

  /* Each mem_ref_t includes the type of reference (read or write),
  * the address referenced, and the size of the reference.
  */
typedef struct _mem_ref_t
{
	bool write;
	void* addr;
	size_t size;
	app_pc pc;
} mem_ref_t;

/* Max number of mem_ref a buffer can have */
#define MAX_NUM_MEM_REFS 16
/* The size of memory buffer for holding mem_refs. When it fills up,
 * we dump data from the buffer to the file.
 */
#define MEM_BUF_SIZE (sizeof(mem_ref_t) * MAX_NUM_MEM_REFS)
 /* Total modules to trace */

 /* thread private log file and counter */
typedef struct per_thread_t
{
	char* buf_ptr;
	char* buf_base;
	/* buf_end holds the negative value of real address of buffer end. */
	ptr_int_t buf_end;
	void* cache;
	uint64 num_refs;
} per_thread_t;

/* Cross-instrumentation-phase data. */
typedef struct
{
	app_pc last_pc;
} instru_data_t;

typedef struct module_info_t
{
	char module_name[32];
	bool loaded;
	ptr_int_t start_addr;
	ptr_int_t end_addr;

}module_info_t;

enum modules
{
	STEAMSERVICE = 0,
	TOTAL_MODULES
};

static size_t page_size;
static client_id_t client_id;
static void* mutex;            /* for multithread support */
static uint64 global_num_refs; /* keep a global memory reference count */
static int tls_index;
static app_pc code_cache;
static module_info_t module_info[TOTAL_MODULES] =
{
	 { "steamservice.dll", false, 0, 0 },
};

static void
event_exit(void);
static void
event_thread_init(void* drcontext);
static void
event_thread_exit(void* drcontext);
static dr_emit_flags_t
event_bb_app2app(void* drcontext, void* tag, instrlist_t* bb, bool for_trace,
	bool translating);
static dr_emit_flags_t
event_bb_analysis(void* drcontext, void* tag, instrlist_t* bb, bool for_trace,
	bool translating, void** user_data);
static dr_emit_flags_t
event_bb_insert(void* drcontext, void* tag, instrlist_t* bb, instr_t* instr,
	bool for_trace, bool translating, void* user_data);
static void
event_module_loaded(void* drcontext, const module_data_t* info,
	bool loaded);

static void
memtrace(int module);
static void
code_cache_init(void);
static void
code_cache_exit(void);
static void
instrument_mem(void* drcontext, instrlist_t* ilist, instr_t* where, app_pc pc,
	instr_t* memref_instr, int pos, bool write, int module);

static bool
is_pc_inside_module(app_pc pc, int module);
bool
is_module_name_equal_and_loaded(char* name, int module);

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char* argv[])
{
	/* We need 2 reg slots beyond drreg's eflags slots => 3 slots */
	drreg_options_t ops = { sizeof(ops), 3, false };
	/* Specify priority relative to other instrumentation operations: */
	drmgr_priority_t priority = { sizeof(priority), /* size of struct */
								  "memtrace",       /* name of our operation */
								  NULL, /* optional name of operation we should precede */
								  NULL, /* optional name of operation we should follow */
								  0 };  /* numeric priority */
	dr_set_client_name("vactrace", NULL);
	page_size = dr_page_size();
	drmgr_init();
	drutil_init();
	client_id = id;
	mutex = dr_mutex_create();
	dr_register_exit_event(event_exit);
	if(!drmgr_register_thread_init_event(event_thread_init) ||
		!drmgr_register_thread_exit_event(event_thread_exit) ||
		!drmgr_register_module_load_event(event_module_loaded) ||
		!drmgr_register_bb_app2app_event(event_bb_app2app, &priority) ||
		!drmgr_register_bb_instrumentation_event(event_bb_analysis, event_bb_insert,
			&priority) ||
		drreg_init(&ops) != DRREG_SUCCESS || !drx_init()) {
		/* something is wrong: can't continue */
		DR_ASSERT(false);
		return;
	}
	tls_index = drmgr_register_tls_field();
	DR_ASSERT(tls_index != -1);

	code_cache_init();
	disassemble_set_syntax(DR_DISASM_INTEL);
	dr_enable_console_printing();
	dr_printf("vactrace is running\n");
}

static void
event_exit()
{
#ifdef SHOW_RESULTS
	char msg[512];
	int len;
	len = dr_snprintf(msg, sizeof(msg) / sizeof(msg[0]),
		"Instrumentation results:\n"
		"  saw %llu memory references\n",
		global_num_refs);
	DR_ASSERT(len > 0);
	NULL_TERMINATE_BUFFER(msg);
	DISPLAY_STRING(msg);
#endif /* SHOW_RESULTS */
	code_cache_exit();

	if(!drmgr_unregister_tls_field(tls_index) ||
		!drmgr_unregister_thread_init_event(event_thread_init) ||
		!drmgr_unregister_thread_exit_event(event_thread_exit) ||
		!drmgr_unregister_bb_insertion_event(event_bb_insert) ||
		drreg_exit() != DRREG_SUCCESS)
		DR_ASSERT(false);

	dr_mutex_destroy(mutex);
	drutil_exit();
	drmgr_exit();
	drx_exit();
}

static void
event_thread_init(void* drcontext)
{
	per_thread_t* data;

	/* allocate thread private data */
	data = dr_thread_alloc(drcontext, sizeof(per_thread_t));
	drmgr_set_tls_field(drcontext, tls_index, data);
	data->buf_base = dr_thread_alloc(drcontext, MEM_BUF_SIZE);
	data->buf_ptr = data->buf_base;
	/* set buf_end to be negative of address of buffer end for the lea later */
	data->buf_end = -(ptr_int_t)(data->buf_base + MEM_BUF_SIZE);
	data->num_refs = 0;
}

static void
event_thread_exit(void* drcontext)
{
	per_thread_t* data;

	// memtrace(drcontext);
	data = drmgr_get_tls_field(drcontext, tls_index);
	dr_mutex_lock(mutex);
	global_num_refs += data->num_refs;
	dr_mutex_unlock(mutex);
	dr_thread_free(drcontext, data->buf_base, MEM_BUF_SIZE);
	dr_thread_free(drcontext, data, sizeof(per_thread_t));
}

/* we transform string loops into regular loops so we can more easily
 * monitor every memory reference they make
 */
static dr_emit_flags_t
event_bb_app2app(void* drcontext, void* tag, instrlist_t* bb, bool for_trace,
	bool translating)
{
	if(!drutil_expand_rep_string(drcontext, bb)) {
		DR_ASSERT(false);
		/* in release build, carry on: we'll just miss per-iter refs */
	}
	if(!drx_expand_scatter_gather(drcontext, bb, NULL)) {
		DR_ASSERT(false);
	}
	return DR_EMIT_DEFAULT;
}

static dr_emit_flags_t
event_bb_analysis(void* drcontext, void* tag, instrlist_t* bb, bool for_trace,
	bool translating, void** user_data)
{
	instru_data_t* data = (instru_data_t*)dr_thread_alloc(drcontext, sizeof(*data));
	data->last_pc = NULL;
	*user_data = (void*)data;
	return DR_EMIT_DEFAULT;
}

/* event_bb_insert calls instrument_mem to instrument every
 * application memory reference.
 */
static dr_emit_flags_t
event_bb_insert(void* drcontext, void* tag, instrlist_t* bb, instr_t* where,
	bool for_trace, bool translating, void* user_data)
{
	int i;
	instru_data_t* data = (instru_data_t*)user_data;
	instr_t* instr_fetch = drmgr_orig_app_instr_for_fetch(drcontext);
	if(instr_fetch != NULL)
		data->last_pc = instr_get_app_pc(instr_fetch);
	app_pc last_pc = data->last_pc;

	for(size_t module = STEAMSERVICE; module != TOTAL_MODULES; module++)
	{
		if(is_pc_inside_module(last_pc, module))
		{
			if(drmgr_is_last_instr(drcontext, where))
				dr_thread_free(drcontext, data, sizeof(*data));

			instr_t* instr_operands = drmgr_orig_app_instr_for_operands(drcontext);
			if(instr_operands == NULL ||
				(!instr_writes_memory(instr_operands) && !instr_reads_memory(instr_operands)))
				return DR_EMIT_DEFAULT;
			DR_ASSERT(instr_is_app(instr_operands));
			DR_ASSERT(last_pc != NULL);

			if(instr_reads_memory(instr_operands))
			{
				for(int i = 0; i < instr_num_srcs(instr_operands); i++)
				{
					if(opnd_is_memory_reference(instr_get_src(instr_operands, i)))
					{
						instrument_mem(drcontext, bb, where, last_pc, instr_operands, i, false, module);
					}
				}
			}

			if(instr_writes_memory(instr_operands))
			{
				for(i = 0; i < instr_num_dsts(instr_operands); i++)
				{
					if(opnd_is_memory_reference(instr_get_dst(instr_operands, i)))
					{
						instrument_mem(drcontext, bb, where, last_pc, instr_operands, i, true, module);
					}
				}
			}
			break;
		}
	}
	return DR_EMIT_DEFAULT;
}

void event_module_loaded(void* drcontext, const module_data_t* info, bool loaded)
{
	const char* name = dr_module_preferred_name(info);

	for(size_t module = STEAMSERVICE; module != TOTAL_MODULES; module++)
	{
		if(is_module_name_equal_and_loaded(name, module))
		{
			dr_printf("%s loaded!\n", module_info[module].module_name);
			module_info[module].loaded = true;
			module_info[module].start_addr = info->start;
			module_info[module].end_addr = info->end;
			break;
		}
	}
}

static void
memtrace(int module)
{
	void* drcontext = dr_get_current_drcontext();

	per_thread_t* data;
	int num_refs;
	mem_ref_t* mem_ref;

	data = drmgr_get_tls_field(drcontext, tls_index);
	mem_ref = (mem_ref_t*)data->buf_base;
	num_refs = (int)((mem_ref_t*)data->buf_ptr - mem_ref);

	byte buf[0x120];

	for(int i = 0; i < num_refs; i++)
	{
		if(dr_safe_read(mem_ref->addr, sizeof(buf), &buf, NULL))
		{
			if(buf[0x12] == 'M' && buf[0x13] == 'Z')
			{
				if(buf[0x52] == 'V' && buf[0x53] == 'L' && buf[0x54] == 'V')
				{
					dr_printf("\nMZ found! memory reference addr: %08x, size: %08x, write: %s\n", mem_ref->addr, mem_ref->size, mem_ref->write ? "true" : "false");
					disassemble(drcontext, mem_ref->pc, STDOUT);
					for(size_t i = 0; i < sizeof(buf); i++)
					{
						dr_printf("%02x ", buf[i]);
					}
					dr_printf("\n");
				}
			}
		}
		++mem_ref;
	}

	memset(data->buf_base, 0, MEM_BUF_SIZE);
	data->num_refs += num_refs;
	data->buf_ptr = data->buf_base;
}

static void
code_cache_init(void)
{
	void* drcontext;
	instr_t* where;
	byte* end;

	drcontext = dr_get_current_drcontext();
	code_cache = dr_nonheap_alloc(page_size, DR_MEMPROT_READ | DR_MEMPROT_WRITE | DR_MEMPROT_EXEC);

	/* different clean calls for each module in the same code cache */
	for(size_t module = STEAMSERVICE; module != TOTAL_MODULES; module++)
	{
		instrlist_t* ilist = instrlist_create(drcontext);
		app_pc code = (app_pc)(((ptr_int_t)code_cache) + (module * 0x64));

		/* The lean procedure simply performs a clean call, and then jumps back
		 * to the DR code cache.
		 */
		where = INSTR_CREATE_jmp_ind(drcontext, opnd_create_reg(DR_REG_XCX));
		instrlist_meta_append(ilist, where);
		/* clean call */
		dr_insert_clean_call(drcontext, ilist, where, (void*)memtrace, false, 1, OPND_CREATE_INT32(module));

		/* Encodes the instructions into memory and then cleans up. */
		end = instrlist_encode(drcontext, ilist, code, false);
		DR_ASSERT((size_t)(end - code) < page_size);
		instrlist_clear_and_destroy(drcontext, ilist);
	}
	/* set the memory as just +rx now */
	dr_memory_protect(code_cache, page_size, DR_MEMPROT_READ | DR_MEMPROT_EXEC);
}

static void
code_cache_exit(void)
{
	dr_nonheap_free(code_cache, page_size);
}

/*
 * instrument_mem is called whenever a memory reference is identified.
 * It inserts code before the memory reference to to fill the memory buffer
 * and jump to our own code cache to call the clean_call when the buffer is full.
 */
static void
instrument_mem(void* drcontext, instrlist_t* ilist, instr_t* where, app_pc pc,
	instr_t* memref_instr, int pos, bool write, int module)
{
	instr_t* instr, * call, * restore;
	opnd_t ref, opnd1, opnd2;
	reg_id_t reg1, reg2;
	drvector_t allowed;
	per_thread_t* data;

	data = drmgr_get_tls_field(drcontext, tls_index);

	/* Steal two scratch registers.
	 * reg2 must be ECX or RCX for jecxz.
	 */
	drreg_init_and_fill_vector(&allowed, false);
	drreg_set_vector_entry(&allowed, DR_REG_XCX, true);
	if(drreg_reserve_register(drcontext, ilist, where, &allowed, &reg2) !=
		DRREG_SUCCESS ||
		drreg_reserve_register(drcontext, ilist, where, NULL, &reg1) != DRREG_SUCCESS) {
		DR_ASSERT(false); /* cannot recover */
		drvector_delete(&allowed);
		return;
	}
	drvector_delete(&allowed);

	if(write)
		ref = instr_get_dst(memref_instr, pos);
	else
		ref = instr_get_src(memref_instr, pos);

	/* use drutil to get mem address */
	drutil_insert_get_mem_addr(drcontext, ilist, where, ref, reg1, reg2);

	/* The following assembly performs the following instructions
	 * buf_ptr->write = write;
	 * buf_ptr->addr  = addr;
	 * buf_ptr->size  = size;
	 * buf_ptr->pc    = pc;
	 * buf_ptr++;
	 * if (buf_ptr >= buf_end_ptr)
	 *    clean_call();
	 */
	drmgr_insert_read_tls_field(drcontext, tls_index, ilist, where, reg2);
	/* Load data->buf_ptr into reg2 */
	opnd1 = opnd_create_reg(reg2);
	opnd2 = OPND_CREATE_MEMPTR(reg2, offsetof(per_thread_t, buf_ptr));
	instr = INSTR_CREATE_mov_ld(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* Move write/read to write field */
	opnd1 = OPND_CREATE_MEM32(reg2, offsetof(mem_ref_t, write));
	opnd2 = OPND_CREATE_INT32(write);
	instr = INSTR_CREATE_mov_imm(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* Store address in memory ref */
	opnd1 = OPND_CREATE_MEMPTR(reg2, offsetof(mem_ref_t, addr));
	opnd2 = opnd_create_reg(reg1);
	instr = INSTR_CREATE_mov_st(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* Store size in memory ref */
	opnd1 = OPND_CREATE_MEMPTR(reg2, offsetof(mem_ref_t, size));
	/* drutil_opnd_mem_size_in_bytes handles OP_enter */
	opnd2 = OPND_CREATE_INT32(drutil_opnd_mem_size_in_bytes(ref, memref_instr));
	instr = INSTR_CREATE_mov_st(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* Store pc in memory ref */
	/* For 64-bit, we can't use a 64-bit immediate so we split pc into two halves.
	 * We could alternatively load it into reg1 and then store reg1.
	 * We use a convenience routine that does the two-step store for us.
	 */
	opnd1 = OPND_CREATE_MEMPTR(reg2, offsetof(mem_ref_t, pc));
	instrlist_insert_mov_immed_ptrsz(drcontext, (ptr_int_t)pc, opnd1, ilist, where, NULL,
		NULL);

	/* Increment reg value by pointer size using lea instr */
	opnd1 = opnd_create_reg(reg2);
	opnd2 = opnd_create_base_disp(reg2, DR_REG_NULL, 0, sizeof(mem_ref_t), OPSZ_lea);
	instr = INSTR_CREATE_lea(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* Update the data->buf_ptr */
	drmgr_insert_read_tls_field(drcontext, tls_index, ilist, where, reg1);
	opnd1 = OPND_CREATE_MEMPTR(reg1, offsetof(per_thread_t, buf_ptr));
	opnd2 = opnd_create_reg(reg2);
	instr = INSTR_CREATE_mov_st(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* we use lea + jecxz trick for better performance
	 * lea and jecxz won't disturb the eflags, so we won't insert
	 * code to save and restore application's eflags.
	 */
	 /* lea [reg2 - buf_end] => reg2 */
	opnd1 = opnd_create_reg(reg1);
	opnd2 = OPND_CREATE_MEMPTR(reg1, offsetof(per_thread_t, buf_end));
	instr = INSTR_CREATE_mov_ld(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);
	opnd1 = opnd_create_reg(reg2);
	opnd2 = opnd_create_base_disp(reg1, reg2, 1, 0, OPSZ_lea);
	instr = INSTR_CREATE_lea(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* jecxz call */
	call = INSTR_CREATE_label(drcontext);
	opnd1 = opnd_create_instr(call);
	instr = INSTR_CREATE_jecxz(drcontext, opnd1);
	instrlist_meta_preinsert(ilist, where, instr);

	/* jump restore to skip clean call */
	restore = INSTR_CREATE_label(drcontext);
	opnd1 = opnd_create_instr(restore);
	instr = INSTR_CREATE_jmp(drcontext, opnd1);
	instrlist_meta_preinsert(ilist, where, instr);

	/* clean call */
	/* We jump to lean procedure which performs full context switch and
	 * clean call invocation. This is to reduce the code cache size.
	 */
	instrlist_meta_preinsert(ilist, where, call);
	/* mov restore DR_REG_XCX */
	opnd1 = opnd_create_reg(reg2);
	/* this is the return address for jumping back from lean procedure */
	opnd2 = opnd_create_instr(restore);
	/* We could use instrlist_insert_mov_instr_addr(), but with a register
	 * destination we know we can use a 64-bit immediate.
	 */
	instr = INSTR_CREATE_mov_imm(drcontext, opnd1, opnd2);
	instrlist_meta_preinsert(ilist, where, instr);

	/* jmp code_cache */
	app_pc code = (app_pc)(((ptr_int_t)code_cache) + (module * 0x64));
	opnd1 = opnd_create_pc(code);
	instr = INSTR_CREATE_jmp(drcontext, opnd1);
	instrlist_meta_preinsert(ilist, where, instr);

	/* Restore scratch registers */
	instrlist_meta_preinsert(ilist, where, restore);
	if(drreg_unreserve_register(drcontext, ilist, where, reg1) != DRREG_SUCCESS ||
		drreg_unreserve_register(drcontext, ilist, where, reg2) != DRREG_SUCCESS)
		DR_ASSERT(false);
}

bool
is_pc_inside_module(app_pc pc, int module)
{
	return pc >= module_info[module].start_addr && pc < module_info[module].end_addr;
}

bool
is_module_name_equal_and_loaded(char* name, int module)
{
	return strcmp(name, module_info[module].module_name) == NULL && module_info[module].loaded == false;
}