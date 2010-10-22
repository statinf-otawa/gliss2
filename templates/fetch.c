/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */

#include <stdlib.h>
#include <stdio.h>
#include <$(proc)/mem.h>
#include <$(proc)/fetch.h>
$(if !is_RISC)#include <$(proc)/gen_int.h>$(end)

#include "fetch_table.h"

#define $(proc)_error(e) fprintf(stderr, "%s\n", (e))


/* Extern Modules */
/* Constants */


/* Variables & Fonctions */

static void halt_fetch(void)
{
}


static void init_fetch(void)
{
}



/* initialization and destruction of $(proc)_fetch_t object */

static int number_of_fetch_objects = 0;


$(proc)_fetch_t *$(proc)_new_fetch($(proc)_platform_t *state)
{
	$(proc)_fetch_t *res = malloc(sizeof($(proc)_fetch_t));
	if (res == NULL)
		$(proc)_error("not enough memory to create a $(proc)_fetch_t object"); /* I assume error handling will remain the same, we use $(proc)_error istead of iss_error ? */
	res->mem = $(proc)_get_memory(state, $(PROC)_MAIN_MEMORY);
	if (number_of_fetch_objects == 0)
		init_fetch();
	number_of_fetch_objects++;
	return res;
}


void $(proc)_delete_fetch($(proc)_fetch_t *fetch)
{
	if (fetch == NULL)
		/* we shouldn't try to free a void fetch_t object, should this output an error ? */
		$(proc)_error("cannot delete an NULL $(proc)_fetch_t object");
	free(fetch);
	number_of_fetch_objects--;
	/*assert(number_of_fetch_objects >= 0);*/
	if (number_of_fetch_objects == 0)
		halt_fetch();
}

$(if is_RISC)
/*
	donne la valeur d'une zone m�moire (une instruction) en ne prenant
	en compte que les bits indiqu�s par le mask

	on fait un ET logique entre l'instruction et le masque,
	on conserve seulement les bits indiqu�s par le masque
	et on les concat�ne pour avoir un nombre sur bits

	on suppose que le masque n'a pas plus de 32 bits � 1,
	sinon d�bordement

	instr : instruction (de $(C_inst_size) bits)
	mask  : masque ($(C_inst_size) bits aussi)
*/
static uint32_t valeur_sur_mask_bloc(uint$(C_inst_size)_t instr, uint$(C_inst_size)_t mask)
{
	int i;
	uint$(C_inst_size)_t tmp_mask;
	uint32_t res = 0;

	/* on fait un parcours du bit de fort poids de instr[0]
	� celui de poids faible de instr[nb_bloc-1], "de gauche � droite" */

	tmp_mask = mask;
	for (i = $(C_inst_size) - 1; i >= 0; i--)
	{
		/* le bit i du mask est 1 ? */
		if (tmp_mask & $(msb_mask))
		{
			/* si oui, recopie du bit i de l'instruction
			� droite du resultat avec decalage prealable */
			res <<= 1;
			res |= ((instr >> i) & 0x01);
		}
		tmp_mask <<= 1;
	}
	return res;
}


/* Fonctions Principales */
$(proc)_ident_t $(proc)_fetch($(proc)_fetch_t *fetch, $(proc)_address_t address, uint$(C_inst_size)_t *code)
{
	uint32_t valeur;
	Table_Decodage *ptr;
	Table_Decodage *ptr2 = table;
	*code = $(proc)_mem_read$(C_inst_size)(fetch->mem, address);

	do
	{
                valeur = valeur_sur_mask_bloc(*code, ptr2->mask);
                ptr  = ptr2;
		ptr2 = ptr->table[valeur].ptr;
	}
	while (ptr->table[valeur].type == TABLEFETCH);

	return ($(proc)_ident_t)ptr->table[valeur].ptr;
}
$(else)

/* here we deal with variable size instructions (CISC) */


/* Fonctions Principales */

/* code must be already initialized so it could contain any instruction (should be init to max size instr) */
$(proc)_ident_t $(proc)_fetch($(proc)_fetch_t *fetch, $(proc)_address_t address, mask_t *code)
{
	uint32_t value;

	Table_Decodage *ptr;
	Table_Decodage *ptr2;
	/* init a buffer for the read instr, size should be max instr size for the given arch */
	/* code is the buffer, its already init */
	/*uint32_t i_buff[$(max_instruction_size) / 32 + ($(max_instruction_size) % 32? 1: 0)];*/
	/*mask_t inst_buff = {i_buff, 0}; */
	ptr2 = table;
	do
	{
		/* if inst buffer has not enough bits to apply mask, read and add what's needed, read a 32 bit chunk (like in mask_t) at a time */
		while (get_mask_length(code) < get_mask_length(ptr2->mask)) {
			set_mask_chunk(code, get_mask_length(code) >> 5, $(proc)_mem_read32(fetch->mem, address + (get_mask_length(code) >> 2)));
			set_mask_length(code, get_mask_length(code) + 32);
		}

		/* compute value on mask */
		value = value_on_mask(code, ptr2->mask);
                ptr  = ptr2;
		ptr2 = ptr->table[value].ptr;
	}
	while (ptr->table[value].type == TABLEFETCH);

	return ($(proc)_ident_t)ptr->table[value].ptr;
}
$(end)
/* End of file $(proc)_fetch.c */
