/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */

#include <stdio.h>
#include <gliss/api.h>
#include <gliss/gen_int.h>

#define gliss_error(e) fprintf(stderr, "%s\n", (e))



int get_mask_length(struct mask_t *mask)
{
	return mask->bit_length;
}

void set_mask_length(struct mask_t *mask, int val)
{
	mask->bit_length = val;
}

/* !!WARNING!! idx is not checked for overflow */
uint32_t get_mask_chunk(struct mask_t *mask, int idx)
{
	return mask->mask[idx];
}

/* !!WARNING!! idx is not checked for overflow */
void set_mask_chunk(struct mask_t *mask, int idx, uint32_t val)
{
	mask->mask[idx] = val;
}


/* for debug */
void output_mask(FILE *out, struct mask_t *mask)
{
	int n32 = mask->bit_length / 32;
	int rem = mask->bit_length % 32;
	int i;
	
	fprintf(out, "[%d]", mask->bit_length);
	for (i = 0; i < n32; i++)
		fprintf(out, "%08X", mask->mask[i]);
	if (rem)
		fprintf("(%d)%08X\n", rem, mask->mask[i]);
}


/* shift a mask 1 bit to the left and add a given bit to the right,
 * mask should be long enough to add one bit */
/*static void mask_left_shift_add_bit(struct mask_t *mask, uint32_t new_lsb)
{
	mask->bit_length++;
	int n = (mask->bit_length / 32) + ((mask->bit_length % 32)? 1: 0);
	uint32_t b1 = new_lsb, b2;
	
	for (int i = 0; i < n; i++) {
		b2 = b1;
		b1 = (0x80000000 & mask->mask[i]) >> 31;
		mask->mask[i] = (mask->mask[i] << 1) | b2;
	}
}*/


/* return bit n of a mask, result (0 or 1) is right justified in an uint32_t */
static uint32_t get_bit_n(struct mask_t *mask, int n)
{
	if (n >= mask->bit_length)
		/* index out of range, should be an error */
		return 0;
	int bit_idx = n % 32;
	int idx = n / 32 + (bit_idx? 1: 0);
	return ((mask->mask[idx] >> bit_idx) & 1);
}


/*static void set_bit_n(struct mask_t *mask, int n, uint32_t bit)
{
	if (n >= mask->bit_length)
		return;
	int bit_idx = n % 32;
	int idx = n / 32 + (bit_idx? 1: 0);
	uint64_t bit_mask = 1 << bit_idx;
	mask->mask[idx] = (mask->mask[idx] & ~bit_mask) | (bit? bit_mask: 0);
}*/


/* returns the bits in a value inst, only those whose position is set in mask,
 * the selected bits are then concatenated to produce a single 32 bit max number
 * inst->bit_length should be >= to mask->bit_length. we hope the result is 32 bit max as
 * it needs to be used as an array index so it mustn't be too huge or, eg., the fetch algorithm might be changed
 */
uint32_t value_on_mask(struct mask_t *inst, struct mask_t *mask)
{
	uint32_t res = 0;
	int k = 0;
	int i;
	
	if (mask->bit_length == 0)
		return 0;
	for (i = mask->bit_length - 1; i >= 0; i--) {
		if (get_bit_n(mask, i)) {
			k++;
			if (k > 32)
				/* should be an error */
				gliss_error("ERROR: a value on mask is more than 32 bit long\n");
			res = ((res << 1) | get_bit_n(inst, i));
		}
	}
	return res;
}

/* same as previous but we can use mask with more than 32 bits (64 max),
 * used to extract instruction parameters during decode
 */
uint64_t extract_mask(struct mask_t *inst, struct mask_t *mask)
{
	uint64_t res = 0;
	int k = 0;
	int i;
	
	if (mask->bit_length == 0)
		return 0;
	for (i = mask->bit_length - 1; i >= 0; i--) {
		if (get_bit_n(mask, i)) {
			k++;
			if (k > 64)
				/* should be an error */
				gliss_error("ERROR: a value on mask is more than 64 bit long\n");
			res = ((res << 1) | get_bit_n(inst, i));
		}
	}
	return res;
}

/* End of file gen_int.c */
