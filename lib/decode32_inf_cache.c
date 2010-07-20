/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <gliss/fetch.h>
#include <gliss/decode.h> /* api.h will be in it, for fetch functions, decode_table.h also */
#include <gliss/config.h> /* for memory endiannesses */

#include "decode_table.h"

#define gliss_error(e) fprintf(stderr, "%s\n", (e))


/* endianness */
typedef enum gliss_endianness_t {
  little = 0,
  big = 1
} gliss_endianness_t;

/* Only works if tablelength == 2^N */
#define INDEX_FOR(tablelength, hash) (hash & (tablelength - 1u))

#ifndef CACHE_SIZE
#define CACHE_SIZE (4096*2) // Must be a power of two
#endif

typedef struct gliss_entry_t {
	gliss_address_t key;
	gliss_inst_t*   value;
    struct gliss_entry_t* next;
}gliss_entry_t;

typedef struct gliss_hashtable_t {
	unsigned int     tablelength;
    gliss_entry_t**  table;
}gliss_hashtable_t;

/* decode structure */
struct gliss_decoder_t
{
    /* the fetch unit used to retrieve instruction ID */
        gliss_fetch_t *fetch;
        gliss_hashtable_t* cache;
};


/** ! Size must be a power of two ! */
static gliss_hashtable_t* create_hashtable (unsigned int size  );
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
	d->cache = create_hashtable( CACHE_SIZE );
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
gliss_inst_t *gliss_decode(gliss_decoder_t *decoder, gliss_address_t address)
{
    gliss_inst_t*  res = 0;
    gliss_ident_t  id;
    uint32_t     code;

    /* Is the instruction inside the cache ? */
    res = hashtable_search(decoder->cache, address);
    if( !res )
    {
        /* If not find : */
        /* first, fetch the instruction at the given address */
        code = gliss_mem_read32(decoder->fetch->mem, address);

        id   = gliss_fetch(decoder->fetch, address, code);
        /* then decode it */
        #ifndef GLISS_NO_MALLOC
        res  = gliss_decode_table[id](code);
        #else
        res = (gliss_inst_t*)malloc(sizeof(gliss_inst_t));
        gliss_decode_table[id](code, res);
        #endif
        res->addr = address;
        
        /* and last cache the instruction */
        hashtable_insert(decoder->cache, address, res);
    }
    return res;
}

static gliss_hashtable_t* create_hashtable( unsigned int size )
{
    gliss_hashtable_t* h;
    unsigned int i;
    /* Check requested hashtable isn't too large */
    assert (size < (1u << 30));
    assert( size  != 0 );
    /* Check requested size and depth is a power of two */
    if( (size &(size -1)) != 0 ) size = pow(2., ceil(log(size ) / log(2.)) );

    h = (gliss_hashtable_t*)malloc( sizeof(gliss_hashtable_t) );
    if (NULL == h) return NULL; /*oom*/

    h->table = (gliss_entry_t **)malloc( sizeof(gliss_entry_t*) * size );
    if (NULL == h->table)
    {
        free(h);
        return NULL;
    } /*oom*/

    for(i = 0; i < size; i++)
        h->table[i] = NULL;

    h->tablelength  = size;
    return h;
}


static void hashtable_insert(gliss_hashtable_t* h, gliss_address_t key, gliss_inst_t* value)
{
    /* This method allows duplicate keys - but they shouldn't be used */
    unsigned int   index;
    gliss_entry_t* entry;
    entry = (gliss_entry_t*)malloc( sizeof(gliss_entry_t) );

    index        = INDEX_FOR(h->tablelength, key);
    entry->key   = key;
    entry->value = value;
    entry->next  = h->table[index];
    h->table[index] = entry;
}


static gliss_inst_t* hashtable_search(gliss_hashtable_t* h, gliss_address_t key)
{
    gliss_entry_t* entry = h->table[INDEX_FOR(h->tablelength, key)];

    while (NULL != entry)
    {
        /* Check hash value to short circuit heavier comparison */
        if (key == entry->key) return entry->value;
        entry = entry->next;
    }

    return NULL;
}

static void hashtable_destroy(gliss_hashtable_t* h)
{
    unsigned int i;
    gliss_entry_t *e, *f;
    gliss_entry_t **table = h->table;

    for (i = 0; i < h->tablelength; i++)
    {
        e = table[i];
        while (NULL != e){
            f = e;
            e = e->next;
			
            free(f->value);
            free(f);
        }
    }

    free(h->table);
    free(h);
}
/* End of file gliss_decode.c */
