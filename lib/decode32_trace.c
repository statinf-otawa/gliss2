/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <gliss/fetch.h>
#include <gliss/decode.h> /* api.h will be in it, for fetch functions, decode_table.h also */
#include <gliss/config.h> /* for memory endiannesses */

#include "decode_table.h"

#ifndef GLISS_NO_MALLOC
#error "GEP option GLISS_NO_MALLOC must be activated when using module decode32_trace"
#endif

#define gliss_error(e) fprintf(stderr, "%s\n", (e))


/* endianness */
typedef enum gliss_endianness_t {
  little = 0,
  big = 1
} gliss_endianness_t;

/* Optimized modulo : only works if tablelength == 2^N */
#define MODULO(x, length) ((x) & ((length) - 1u))

#ifndef CACHE_DEPTH
#define CACHE_DEPTH 8     // Must be greater or equal to 2
#endif
#ifndef CACHE_SIZE
#define CACHE_SIZE (4096) // Must be a power of 2
#endif

// Double linked list (linked as a ring)
typedef struct gliss_entry {

    gliss_address_t  key;
    gliss_inst_t     value[TRACE_DEPTH];

    struct gliss_entry* next;
}gliss_entry_t;

typedef struct gliss_hashtable {
    gliss_entry_t* entry_tab;
    gliss_entry_t* table[CACHE_SIZE];
}gliss_hashtable_t;


/* decode structure */
struct gliss_decoder_t
{
    /* the fetch unit used to retrieve instruction ID */
    gliss_fetch_t *fetch;
    gliss_hashtable_t* cache;

};

/** ! Size must be a power of two ! */
static gliss_hashtable_t* create_hashtable (unsigned int size, unsigned int depth);
static void hashtable_destroy(gliss_hashtable_t* h );
static void hashtable_insert(gliss_hashtable_t* h, gliss_address_t key, gliss_inst_t* value);
static gliss_inst_t* hashtable_search(gliss_hashtable_t* h, gliss_address_t key);


/* Extern Modules */
/* Constants */
/* Variables & Fonctions */
/* decoding */
gliss_inst_t *gliss_decode(gliss_decoder_t *decoder, gliss_address_t address);


/* initialization and destruction of gliss_decode_t object */
static int number_of_decoder_objects = 0;

static void init_decoder(gliss_decoder_t *d, gliss_platform_t *state)
{
        d->fetch = gliss_new_fetch(state);
        d->cache = create_hashtable( CACHE_SIZE, CACHE_DEPTH );

}

static void halt_decoder(gliss_decoder_t *d)
{
        gliss_delete_fetch(d->fetch);
        hashtable_destroy(d->cache);

}

gliss_decoder_t *gliss_new_decoder(gliss_platform_t *state)
{
    gliss_decoder_t *res = malloc(sizeof(gliss_decoder_t));
    if (res == NULL)
                gliss_error("not enough memory to create a gliss_decoder_t object"); /* I assume error handling will remain the same, we use gliss_error istead of iss_error ? */
    /*assert(number_of_decode_objects >= 0);*/
    init_decoder(res, state);
    number_of_decoder_objects++;
    return res;
}

void gliss_delete_decoder(gliss_decoder_t *decode)
{
    if (decode == NULL)
        /* we shouldn't try to free a void decoder_t object, should this output an error ? */
                gliss_error("cannot delete an NULL gliss_decoder_t object");
    number_of_decoder_objects--;
    /*assert(number_of_decode_objects >= 0);*/
    halt_decoder(decode);
    free(decode);
}

/* Fonctions Principales */
/** @brief Decode a block of instructions
 *  Simulated programmed is split into regular parts of size TRACE_DEPTH.
 *  gliss_decode() decode an entire block of instruction belonging to the given
 *  address and return the pointer of the first element of the block.
 *  It is left to the user to compute the right offset inside the block 
 *  (knowing the eddresse and TRACE_DEPTH)
 * 
 *  @param decoder
 *  @param address inside a block of instruction to decode
 *  @return first element of an array of instructions 
 * */
gliss_inst_t* gliss_decode(gliss_decoder_t *decoder, gliss_address_t address)
{
	gliss_inst_t*  res = 0;
    gliss_ident_t  id;
    uint32_t     code;

    // Is the instruction inside the cache ? ===========================
    unsigned int    i;
    
    /*  A block of four elements :
     *  ____
     *  |  | <- block_addr 
     *  ----
     *  |  |
     *  ----
     *  |  | <- address  
     *  ---- 
     *  |  |
     *  ____
     * */
    gliss_address_t block_addr = (address >> TRACE_DEPTH_PW >> 2 ) << TRACE_DEPTH_PW << 2; // (address / TRACE_DEPTH / 4) * TRACE_DEPTH * 4
    unsigned int    hash       = MODULO(block_addr >> 2 >> TRACE_DEPTH_PW, CACHE_SIZE);    // (block_addr / 4 / TRACE_DEPTH) % CACHE_SIZE

    gliss_entry_t** table  = decoder->cache->table;
    gliss_entry_t* current = table[hash];
    gliss_entry_t* init    = current;
    gliss_entry_t* prev;

    // If it's the first element no need to handle LRU policy
    if(block_addr == current->key)
        return current->value;

    prev     = current;
    current  = current->next;

    // "FOR" has the advantage that gcc can unroll the loop if necessary
    // Anyway I've not seen any improvements by unrolling manualy this loop
    for( i = 0; i < (CACHE_DEPTH-2); i++)
    {
        if (block_addr == current->key)
        {
            prev->next     = current->next;
            current->next  = init;
            table[hash] = current;
			return current->value;
        }
        prev     = current;
        current  = current->next;
    }

    // If it's last element LRU can be simplify
    current->next  = init;
    //prev->next = NULL; useless because we don't rely on that
    table[hash] = current;
    
    if (block_addr == current->key)
    {
        return current->value;
    }

    // If not find : --------------------------------------------------
    current->key = block_addr;
    res = (current->value);
    for(i=0; i < TRACE_DEPTH; i++)
    {
        code = gliss_mem_read32(decoder->fetch->mem, block_addr + i*4);
        id   = gliss_fetch(decoder->fetch, block_addr + i*4, code);

        gliss_decode_table[id](code, (res+i));
        (res+i)->addr = block_addr + i*4;
    }
    return res;
}

/**
 * @param depth  must greater or equal to 2
 */
static gliss_hashtable_t* create_hashtable( unsigned int size, unsigned int depth )
{
    gliss_entry_t* init;
    gliss_entry_t* tmp0;
    gliss_entry_t* tmp1;
    gliss_hashtable_t* h;
    unsigned int i, j;
    /* Check requested hashtable isn't too large */
    assert (size < (1u << 30));
    assert( size  != 0 );
    assert( depth >= 2 );
    /* Chech requested size and depth is a power of two */
    if( (size &(size -1)) != 0 ) size  = pow(2., ceil(log(size ) / log(2.)) );

    h = (gliss_hashtable_t*)malloc( sizeof(gliss_hashtable_t) );
    if (NULL == h) return NULL;

    // Allocate table and every chained list with one malloc for better host cache handling
    h->entry_tab = (gliss_entry_t*)malloc(sizeof(gliss_entry_t)*depth*size);

    for(i = 0; i < size; ++i)
    {
        init = h->entry_tab + i*depth;
        if( init == NULL)
        {
            hashtable_destroy(h);
            return NULL;
        }
        tmp0 = init;
        init->key   = -1;

        for(j = 0; j < (depth-1); ++j)
        {
            tmp1 = h->entry_tab + i*depth +j+1;
            if( tmp1 == NULL)
            {
                hashtable_destroy(h);
                return NULL;
            }
            tmp1->key   = -1;

            tmp0->next = tmp1;
            tmp0       = tmp1;
        }
        tmp1->next  = NULL;
        h->table[i] = init;
    }

    return h;
}

static void hashtable_destroy(gliss_hashtable_t* h)
{
    unsigned int i, j;
    gliss_entry_t** table;
    gliss_entry_t*  init;
    gliss_entry_t*  it;
    gliss_entry_t*  tmp;

    if( h != NULL )
    {
		table = h->table;
        if( table != NULL )
        {
            for (i = 0; i < CACHE_SIZE; i++)
            {
                init = table[i];
                it   = init;

                for (j = 0; j < CACHE_DEPTH; j++)
                {
                    if(it != NULL)
                    {
						tmp = it;
                        // Erase each entry
                        it = it->next;
                    }
                    else
                        break;
                }
            }
        }
        // Erase every chained list :
        free( h->entry_tab);
        // Erase gliss_hashtable_t
        free(h);
    }
    

}


/* End of file gliss_decode.c */
