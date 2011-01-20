/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */

#include <stdlib.h>
#include <stdio.h>
#include <$(proc)/mem.h>
#include <$(proc)/fetch.h>
$(if is_CISC_present)#include <$(proc)/gen_int.h>$(end)

#include <$(proc)/macros.h>
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


$(proc)_fetch_t *$(proc)_new_fetch($(proc)_platform_t *pf$(if is_multi_set), $(proc)_state_t *state$(end))
{
	$(proc)_fetch_t *res = malloc(sizeof($(proc)_fetch_t));
	if (res == NULL)
		$(proc)_error("not enough memory to create a $(proc)_fetch_t object"); /* I assume error handling will remain the same, we use $(proc)_error istead of iss_error ? */
	res->mem = $(proc)_get_memory(pf, $(PROC)_MAIN_MEMORY);
	$(if is_multi_set)res->state = state;$(end)
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


$(if is_multi_set)
$(foreach instr_sets_sizes)
$(if is_RISC_size)/*
	donne la valeur d'une zone m�moire (une instruction) en ne prenant
	en compte que les bits indiqu�s par le mask

	on fait un ET logique entre l'instruction et le masque,
	on conserve seulement les bits indiqu�s par le masque
	et on les concat�ne pour avoir un nombre sur bits

	on suppose que le masque n'a pas plus de $(C_size) bits � 1,
	sinon d�bordement

	instr : instruction (de $(C_size) bits)
	mask  : masque ($(C_size) bits aussi)
*/
static uint$(C_size)_t valeur_sur_mask_bloc$(C_size)(uint$(C_size)_t instr, uint$(C_size)_t mask)
{
	int i;
	uint$(C_size)_t tmp_mask;
	uint$(C_size)_t res = 0;

	/* on fait un parcours du bit de fort poids de instr[0]
	� celui de poids faible de instr[nb_bloc-1], "de gauche � droite" */

	tmp_mask = mask;
	for (i = $(C_size) - 1; i >= 0; i--)
	{
		/* le bit i du mask est 1 ? */
		if (tmp_mask & $(msb_size_mask))
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

$(proc)_ident_t $(proc)_fetch_$(C_size)($(proc)_fetch_t *fetch, $(proc)_address_t address, uint$(C_size)_t *code, Table_Decodage_$(C_size) *table)
{
	uint$(C_size)_t valeur;
	Table_Decodage_$(C_size) *ptr;
	Table_Decodage_$(C_size) *ptr2 = table;
	*code = $(proc)_mem_read$(C_size)(fetch->mem, address);

	do
	{
                valeur = valeur_sur_mask_bloc$(C_size)(*code, ptr2->mask);
                ptr  = ptr2;
		ptr2 = ptr->table[valeur].ptr;
	}
	while (ptr->table[valeur].type == TABLEFETCH);

	return ($(proc)_ident_t)ptr->table[valeur].ptr;
}
$(else)/* code must be already initialized so it could contain any instruction (should be init to max size instr) */
$(proc)_ident_t $(proc)_fetch_CISC($(proc)_fetch_t *fetch, $(proc)_address_t address, mask_t *code, Table_Decodage_$(C_size) *table)
{
	uint32_t value;

	Table_Decodage_CISC *ptr;
	Table_Decodage_CISC *ptr2 = table;
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
$(end)$(end)$(end)
$(if !is_multi_set)
$(if is_RISC)
/*
	donne la valeur d'une zone m�moire (une instruction) en ne prenant
	en compte que les bits indiqu�s par le mask

	on fait un ET logique entre l'instruction et le masque,
	on conserve seulement les bits indiqu�s par le masque
	et on les concat�ne pour avoir un nombre sur bits

	on suppose que le masque n'a pas plus de $(C_inst_size) bits � 1,
	sinon d�bordement

	instr : instruction (de $(C_inst_size) bits)
	mask  : masque ($(C_inst_size) bits aussi)
*/
static uint$(C_inst_size)_t valeur_sur_mask_bloc(uint$(C_inst_size)_t instr, uint$(C_inst_size)_t mask)
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
	uint$(C_inst_size)_t valeur;
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
	Table_Decodage *ptr2 = table;
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
$(end)$(end)

$(if is_multi_set)
$(proc)_ident_t $(proc)_fetch($(proc)_fetch_t *fetch, $(proc)_address_t address, code_t *code)
{
	$(proc)_state_t *state = fetch->state;
	$(foreach instruction_sets)
	if ($(select_iset)) {
		$(if is_RISC_iset)return $(proc)_fetch_$(C_size_iset)(fetch, address, &code->u$(C_size_iset), table_$(idx));
		$(else)return $(proc)_fetch_CISC(fetch, address, code->mask, table_$(idx))$(end)
	}
	$(end)
}

$(end)
/* End of file $(proc)_fetch.c */
