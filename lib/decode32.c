/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */

#include <stdlib.h>
#include <stdio.h>
/* #include <math.h>  needed for affiche_valeur_binaire (which is not well coded) */

#include "decode.h" /* api.h will be in it, for fetch functions, decode_table.h also */
#include "config.h"

#define gliss_error(e) fprintf(stderr, (e))

/* decode structure */
struct gliss_decoder_t
{
	/* the fetch unit used to retrieve instruction ID */
	gliss_fetch_t *fetch;
};

/* Extern Modules */
/* Constants */


/* Variables & Fonctions */

/* decoding */
ppc_inst_t *ppc_decode(ppc_decoder_t *decoder, ppc_address_t address);
void ppc_free_inst(ppc_inst_t *inst);


/* initialization and destruction of gliss_decode_t object */

static int number_of_decoder_objects = 0;

static void init_decoder(gliss_decoder_t *d, gliss_platform_t *state)
{
	d->fetch = gliss_new_fetch(state);
}

static void halt_decoder(gliss_decoder_t *d)
{
	gliss_delete_fetch(d->fetch);
}

gliss_decoder_t *gliss_new_decoder(gliss_platform_t *state)
{
	gliss_decoder_t *res = malloc(sizeof(gliss_decoder_t));
	if (res == NULL)
		gliss_error("not enough memory to create a gliss_decoder_t object"); /* I assume error handling will remain the same, we use gliss_error istead of iss_error ? */
	res->mem = gliss_get_memory(state, GLISS_MAIN_MEMORY);
	/*assert(number_of_decode_objects >= 0);*/
	init_decoder(res, state);
	number_of_decode_objects++;
	return res;
}

void gliss_delete_decoder(gliss_decoder_t *decode)
{
	if (decode == NULL)
		/* we shouldn't try to free a void decoder_t object, should this output an error ? */
		gliss_error("cannot delete an NULL gliss_decoder_t object");
	number_of_decode_objects--;
	/*assert(number_of_decode_objects >= 0);*/
	halt_decoder(decode);
	free(decode);
}


/* copied from loader.c */
static int is_host_little(void)
{
    uint32_t x;
    x = 0xDEADBEEF;
    return ( ((unsigned char) x) == 0xEF );
}

/* Fonctions Principales */

gliss_inst_t *gliss_decode(gliss_decoder_t *decoder, gliss_address_t address)
{
	/* first, fetch the instruction at the given address */

	gliss_inst_t *res = 0;
	gliss_ident_t id = gliss_fetch(decoder->fetch, address);
	uint32_t code = gliss_mem_read32(decoder->fetch->mem, address);
	/* revert bytes if endianness of host and target are not equals */
	if (HOST_ENDIANNESS != TARGET_ENDIANNESS)
		code = ((code&0x0FF)<<24)|((code&0x0FF00)<<8)|((code&0x0FF0000)>>8)|((code&0xFF000000)>>24);
	
	/* then decode it */
	
	return gliss_decode_table[id](code);
}


/* End of file gliss_fetch.c */