/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <$(proc)/fetch.h>
#include <$(proc)/decode.h> /* api.h will be in it, for fetch functions, decode_table.h also */
#include <$(proc)/config.h> /* for memory endiannesses */

#include "decode_table.h"

#define $(proc)_error(e) fprintf(stderr, "%s\n", (e))


/* endianness */
typedef enum $(proc)_endianness_t {
	little = 0,
	big = 1
} $(proc)_endianness_t;

/* decode structure */
struct $(proc)_decoder_t
{
	/* the fetch unit used to retrieve instruction ID */
	$(proc)_fetch_t *fetch;
$(if is_multi_set)	/* help determine which decode type if several instr sets defined */
	$(proc)_state_t *state;
	$(proc)_platform_t *pf;$(end)
$(if GLISS_NO_MALLOC)
    $(proc)_inst_t*  tmp_inst;
$(end)
};

/* Extern Modules */
/* Constants */
/* Variables & Fonctions */
/* decoding */
$(proc)_inst_t *$(proc)_decode($(proc)_decoder_t *decoder, $(proc)_address_t address);


/* initialization and destruction of $(proc)_decode_t object */
static int number_of_decoder_objects = 0;

static void init_decoder($(proc)_decoder_t *d, $(proc)_platform_t *pf)
{
	$(if is_multi_set)d->fetch = NULL;
	d->state = NULL;
	d->pf = pf;
	$(else)d->fetch = $(proc)_new_fetch(pf);
	$(end)
$(if GLISS_NO_MALLOC)
        d->tmp_inst = ($(proc)_inst_t*)malloc(sizeof($(proc)_inst_t));
$(end)
}

static void halt_decoder($(proc)_decoder_t *d)
{
        $(proc)_delete_fetch(d->fetch);
$(if GLISS_NO_MALLOC)
        free(d->tmp_inst);
$(end)     
}

$(proc)_decoder_t *$(proc)_new_decoder($(proc)_platform_t *pf)
{
    $(proc)_decoder_t *res = malloc(sizeof($(proc)_decoder_t));
    if (res == NULL)
                $(proc)_error("not enough memory to create a $(proc)_decoder_t object"); /* I assume error handling will remain the same, we use $(proc)_error istead of iss_error ? */
    /*assert(number_of_decode_objects >= 0);*/
    init_decoder(res, pf);
    number_of_decoder_objects++;
    return res;
}

void $(proc)_delete_decoder($(proc)_decoder_t *decode)
{
    if (decode == NULL)
        /* we shouldn't try to free a void decoder_t object, should this output an error ? */
                $(proc)_error("cannot delete an NULL $(proc)_decoder_t object");
    number_of_decoder_objects--;
    /*assert(number_of_decode_objects >= 0);*/
    halt_decoder(decode);
    free(decode);
    
}

/** set the state which is used to determine which instruction set we decode for,
 *  selection conditions are expressions using some state registers,
 *  the registers of the given state will be used after a call to this function.
 *  The fetch object will be created here for multi set descriptions.
 *  Does nothing if only one instr set is defined.
*/
void $(proc)_set_cond_state($(proc)_decoder_t *decoder, $(proc)_state_t *state)
{
	$(if is_multi_set)if (decoder == NULL)
                $(proc)_error("cannot set cond state for a NULL $(proc)_decoder_t object");
	if (state == NULL)
                $(proc)_error("cannot set cond state with a NULL $(proc)_state_t object");
	decoder->state = state;
	/* state is given, we can finally create fetch object here */
	decoder->fetch = $(proc)_new_fetch(decoder->pf, state);
	$(end)

}


$(if !is_multi_set)
$(if is_RISC)
/* Fonctions Principales */
$(proc)_inst_t *$(proc)_decode($(proc)_decoder_t *decoder, $(proc)_address_t address)
{
	$(proc)_inst_t *res = 0;
	$(proc)_ident_t id;
	uint$(C_inst_size)_t code;

	/* first, fetch the instruction at the given address */
	id = $(proc)_fetch(decoder->fetch, address, &code);
	
	/* then decode it */
$(if GLISS_NO_MALLOC)
	res = decoder->tmp_inst;
	$(proc)_decode_table[id](code, res);
$(else)
	res = $(proc)_decode_table[id](code);
$(end)
	res->addr = address;
    
	return res;
}
$(else)
/* Fonctions Principales */
$(proc)_inst_t *$(proc)_decode($(proc)_decoder_t *decoder, $(proc)_address_t address)
{
	$(proc)_inst_t *res = 0;
	$(proc)_ident_t id;
	/* init a buffer for the read instr, size should be max instr size for the given arch */
	uint32_t i_buff[$(max_instruction_size) / 32 + ($(max_instruction_size) % 32? 1: 0)];
	mask_t code = {i_buff, 0};

	/* first, fetch the instruction at the given address */
	id = $(proc)_fetch(decoder->fetch, address, &code);
	/* then decode it */
$(if !GLISS_NO_MALLOC)
	res  = $(proc)_decode_table[id](&code);
$(else)
	res = decoder->tmp_inst;
	$(proc)_decode_table[id](&code, res);
$(end)
	res->addr = address;
        
	return res;
}
$(end)$(end)

$(if is_multi_set)
$(foreach instr_sets_sizes)
/* Fonctions Principales */
$(proc)_inst_t *$(proc)_decode_$(if is_RISC_size)$(C_size)$(else)CISC$(end)($(proc)_decoder_t *decoder, $(proc)_address_t address)
{
	$(proc)_inst_t *res = 0;
	$(proc)_ident_t id;
	code_t code;
	$(if !is_RISC_size)/* init a buffer for the read instr, size should be max instr size for the given arch */
	uint32_t i_buff[$(max_instruction_size) / 32 + ($(max_instruction_size) % 32? 1: 0)];
	code.mask = {i_buff, 0};$(end)

	/* first, fetch the instruction at the given address */
	id = $(proc)_fetch(decoder->fetch, address, &code);
	
	/* then decode it */
$(if GLISS_NO_MALLOC)
	res = decoder->tmp_inst;
	$(proc)_decode_table[id](&code, res);
$(else)
	res = $(proc)_decode_table[id](&code);
$(end)
	res->addr = address;
    
	return res;
}
$(end)

$(if is_multi_set)/* decoding functions for one specific instr set */

/* access to a speicific fetch table */
#include "fetch_table.h"
$(foreach instruction_sets)/* decoding function for instr set $(idx), named $(iset_name) */
$(proc)_inst_t *$(proc)_decode_$(iset_name)($(proc)_decoder_t *decoder, $(proc)_address_t address)
{
	$(proc)_inst_t *res = 0;
	$(proc)_ident_t id;
	code_t code;
	$(if !is_RISC_iset)/* init a buffer for the read instr, size should be max instr size for the given arch */
	uint32_t i_buff[$(max_instruction_size) / 32 + ($(max_instruction_size) % 32? 1: 0)];
	code.mask = {i_buff, 0};$(end)

	/* first, fetch the instruction at the given address, call specialized fetch */
	$(if is_RISC_iset)id = $(proc)_fetch_$(C_size_iset)(decoder->fetch, address, &code.u$(C_size_iset), table_$(idx));
	$(else)id = $(proc)_fetch_CISC(decoder->fetch, address, &code.mask, table_$(idx));$(end)
	
	/* then decode it */
$(if GLISS_NO_MALLOC)
	res = decoder->tmp_inst;
	$(proc)_decode_table[id](&code, res);
$(else)
	res = $(proc)_decode_table[id](&code);
$(end)
	res->addr = address;
    
	return res;
}
$(end)

$(proc)_inst_t *$(proc)_decode($(proc)_decoder_t *decoder, $(proc)_address_t address)
{
	$(proc)_state_t *state = decoder->state;
	$(foreach instruction_sets)
	if ($(select_iset)) {
		$(if is_RISC_iset)return $(proc)_decode_$(C_size_iset)(decoder, address);
		$(else)return $(proc)_decode_CISC(decoder, address)$(end)
	}
	$(end)
}

$(end)

/* End of file $(proc)_decode.c */
