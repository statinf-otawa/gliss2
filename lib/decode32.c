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

/* Optimized modulo : only works if tablelength == 2^N */
#define MODULO(x, length) (x & (length - 1u))

#if defined(GLISS_INF_DECODE_CACHE) && !defined(GLISS_FIXED_DECODE_CACHE) && !defined(GLISS_LRU_DECODE_CACHE)

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
#endif // GLISS_INF_DECODE_CACHE && !GLISS_FIXED_DECODE_CACHE

#if defined(GLISS_FIXED_DECODE_CACHE) && !defined(GLISS_LRU_DECODE_CACHE)

    #ifndef CACHE_DEPTH
    #define CACHE_DEPTH 8     // Must be a power of two
    #endif
    #ifndef CACHE_SIZE
    #define CACHE_SIZE (4096) // Must be a power of two
    #endif

    typedef struct gliss_entry {
        gliss_address_t key;
        gliss_inst_t*   value;
    }gliss_entry_t;

    typedef struct gliss_entry_ring{
        gliss_entry_t* entries;
        unsigned int   idx;
    }gliss_entry_ring_t;

    typedef struct gliss_hashtable {
        unsigned int tablelength; // Table size
        unsigned int tabledepth;  // Nb entries per table cell
        gliss_entry_ring_t** table;
    }gliss_hashtable_t;
#endif // GLISS_FIXED_DECODE_CACHE && !GLISS_LRU_DECODE_CACHE

#if defined(GLISS_LRU_DECODE_CACHE)

    #ifndef CACHE_DEPTH
    #define CACHE_DEPTH 8     // Must be greater or equal to 2
    #endif
    #ifndef CACHE_SIZE
    #define CACHE_SIZE (4096) // Must be a power of 2
    #endif

    // Double linked list (linked as a ring)
    typedef struct gliss_entry {
        #ifndef GLISS_DCACHE_WITH_INSTR_WORD
        gliss_address_t     key;
        #else
        uint32_t            key;
        #endif
        
        #ifndef GLISS_NO_MALLOC
        gliss_inst_t*       value;
        #else
        gliss_inst_t        value;
        #endif
        
        struct gliss_entry* next;
    }gliss_entry_t;

    typedef struct gliss_hashtable {
        gliss_entry_t* entry_tab;
        gliss_entry_t* table[CACHE_SIZE];
    }gliss_hashtable_t;



#endif // GLISS_LRU_DECODE_CACHE

/* decode structure */
struct gliss_decoder_t
{
    /* the fetch unit used to retrieve instruction ID */
        gliss_fetch_t *fetch;
        #if defined(GLISS_INF_DECODE_CACHE) || defined(GLISS_FIXED_DECODE_CACHE) || defined(GLISS_LRU_DECODE_CACHE)
        gliss_hashtable_t* cache;
        #endif
};

#if defined(GLISS_INF_DECODE_CACHE) || defined(GLISS_FIXED_DECODE_CACHE) || defined(GLISS_LRU_DECODE_CACHE)
/** ! Size must be a power of two ! */
#if defined(GLISS_FIXED_DECODE_CACHE) || defined(GLISS_LRU_DECODE_CACHE)
static gliss_hashtable_t* create_hashtable (unsigned int size, unsigned int depth);
#else
static gliss_hashtable_t* create_hashtable (unsigned int size  );
#endif

static void hashtable_destroy(gliss_hashtable_t* h );
static void hashtable_insert(gliss_hashtable_t* h, gliss_address_t key, gliss_inst_t* value);
static gliss_inst_t* hashtable_search(gliss_hashtable_t* h, gliss_address_t key);
#endif // GLISS_INF_DECODE_CACHE || GLISS_FIXED_DECODE_CACHE || GLISS_LRU_DECODE_CACHE

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
        #if defined(GLISS_FIXED_DECODE_CACHE) || defined(GLISS_LRU_DECODE_CACHE)
            d->cache = create_hashtable( CACHE_SIZE, CACHE_DEPTH );
        #elif defined(GLISS_INF_DECODE_CACHE)
            d->cache = create_hashtable( CACHE_SIZE );
        #endif
}

static void halt_decoder(gliss_decoder_t *d)
{
        gliss_delete_fetch(d->fetch);
        #if defined(GLISS_INF_DECODE_CACHE) || defined(GLISS_FIXED_DECODE_CACHE) || defined(GLISS_LRU_DECODE_CACHE)
        hashtable_destroy(d->cache);
        #endif
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

    #ifdef GLISS_DCACHE_WITH_INSTR_WORD
    code = gliss_mem_read32(decoder->fetch->mem, address);
    #endif

    /* Is the instruction inside the cache ? */
#if defined(GLISS_LRU_DECODE_CACHE)
    unsigned int i;
    unsigned int  hash   = MODULO(address, CACHE_SIZE);
    gliss_entry_t** table  = decoder->cache->table;
    gliss_entry_t* current = table[hash];
    gliss_entry_t* init    = current;
    gliss_entry_t* prev;

    // If it's the first element no need to handle LRU policy
    #ifndef GLISS_DCACHE_WITH_INSTR_WORD
    if(address == current->key)
        #ifndef GLISS_NO_MALLOC
        return current->value;
        #else
        return &(current->value);
        #endif        
    #else
    if(code == current->key)
        #ifndef GLISS_NO_MALLOC
        return current->value;
        #else
        return &(current->value);
        #endif   
    #endif

    prev     = current;
    current  = current->next;

    // "FOR" has the advantage that gcc can unroll the loop if necessary
    // Anyway I've not seen any improvements by unrolling manualy this loop
    for( i = 0; i < (CACHE_DEPTH-2); i++)
    {
        #ifndef GLISS_DCACHE_WITH_INSTR_WORD
        if (address == current->key)
        #else
        if (code == current->key)
        #endif
        {
            prev->next     = current->next;
            current->next  = init;
            table[hash] = current;
            #ifndef GLISS_NO_MALLOC
			return current->value;
			#else
			return &(current->value);
			#endif 
        }
        prev     = current;
        current  = current->next;
    }

    // If it's last element LRU can be simplify
    current->next  = init;
    //prev->next = NULL; useless because we don't rely on that
    table[hash] = current;
    
    #ifndef GLISS_DCACHE_WITH_INSTR_WORD
    if (address == current->key)
    #else
    if (code == current->key)
    #endif
    {
        #ifndef GLISS_NO_MALLOC
        return current->value;
        #else
        return &(current->value);
        #endif 
    }
#elif defined(GLISS_INF_DECODE_CACHE) || defined(GLISS_FIXED_DECODE_CACHE)
    res = hashtable_search(decoder->cache, address);

    if( !res )
    {
#endif
        /* If not find : */
        /* first, fetch the instruction at the given address */
        #ifndef GLISS_DCACHE_WITH_INSTR_WORD
        code = gliss_mem_read32(decoder->fetch->mem, address);
        #endif

        id   = gliss_fetch(decoder->fetch, address, code);
        /* then decode it */
        #ifndef GLISS_NO_MALLOC
        res  = gliss_decode_table[id](address, code);
        #else
        gliss_decode_table[id](address, code, &(current->value));
        #endif
        
        /* and last cache the instruction */
#if defined(GLISS_LRU_DECODE_CACHE)
        #ifndef GLISS_DCACHE_WITH_INSTR_WORD
        current->key   = address;
        #else
        current->key   = code;
        #endif
        #ifndef GLISS_NO_MALLOC
		free(current->value);
        current->value = res;
        #endif
#elif defined(GLISS_INF_DECODE_CACHE) || defined(GLISS_FIXED_DECODE_CACHE)
        hashtable_insert(decoder->cache, address, res);
    }

#endif
    #ifndef GLISS_NO_MALLOC
    return current->value;
    #else
    return &(current->value);
    #endif 
}

#if defined(GLISS_INF_DECODE_CACHE) && !defined(GLISS_FIXED_DECODE_CACHE) && !defined(GLISS_LRU_DECODE_CACHE)

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



/* Only works if tablelength == 2^N */
#define INDEX_FOR(tablelength, hash) (hash & (tablelength - 1u))

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

#endif // GLISS_INF_DECODE_CACHE && !GLISS_FIXED_DECODE_CACHE && || !GLISS_LRU_DECODE_CACHE

#if defined(GLISS_FIXED_DECODE_CACHE) && !defined(GLISS_LRU_DECODE_CACHE)

static gliss_hashtable_t* create_hashtable( unsigned int size, unsigned int depth )
{
    gliss_hashtable_t* h;
    unsigned int i, j;
    /* Check requested hashtable isn't too large */
    assert (size < (1u << 30));

    assert( size  != 0 );
    assert( depth != 0 );
    /* Chech requested size and depth is a power of two */
    if( (size &(size -1)) != 0 ) size  = pow(2., ceil(log(size ) / log(2.)) );
    if( (depth&(depth-1)) != 0 ) depth = pow(2., ceil(log(depth) / log(2.)) );

    h = (gliss_hashtable_t*)malloc( sizeof(gliss_hashtable_t) );
    if (NULL == h) return NULL; /*oom*/

    h->table = (gliss_entry_ring_t **)malloc( sizeof(gliss_entry_ring_t*) * size );
    if (NULL == h->table)
    {
        free(h);
        return NULL;
    } /*oom*/

    for(i = 0; i < size; ++i)
    {
        h->table[i] = (gliss_entry_ring_t *)malloc(sizeof(gliss_entry_ring_t));
        if( h->table[i] == NULL)
        {
            hashtable_destroy(h);
            return NULL;
        }

        h->table[i]->idx = 0;
        h->table[i]->entries = (gliss_entry_t*)malloc(sizeof(gliss_entry_t)*depth);

        if( h->table[i]->entries == NULL)
        {
            hashtable_destroy(h);
            return NULL;
        }

        for(j = 0; j < depth; ++j)
        {
            h->table[i]->entries[j].key   = -1;
            h->table[i]->entries[j].value = NULL;/// TODO Carrement allouer l'instruction � l'avance.
        }
    }

    h->tablelength  = size;
    h->tabledepth   = depth;

    return h;
}


static void hashtable_insert(gliss_hashtable_t* h, gliss_address_t key, gliss_inst_t* value)
{
    /* This method allows duplicate keys - but they shouldn't be used */
    /* Insert always erase the oldest entry of the ring               */
    gliss_entry_ring_t* ring = h->table[MODULO(key, h->tablelength)];

    ring->entries[ring->idx].key   = key;
    if( ring->entries[ring->idx].value != NULL )
        free(ring->entries[ring->idx].value );
    ring->entries[ring->idx].value = value;

    ring->idx = MODULO((ring->idx+1), h->tabledepth);
}


static gliss_inst_t* hashtable_search(gliss_hashtable_t* h, gliss_address_t key)
{
    unsigned int i;
    gliss_address_t tmp_key;
    gliss_inst_t*   tmp_value;
    gliss_entry_ring_t* ring = h->table[MODULO(key, h->tablelength)];

    i = ring->idx;
    do{
        /* Check hash value to short circuit heavier comparison */
        if (key == ring->entries[i].key) return ring->entries[i].value;

        i = MODULO((i-1), h->tabledepth);
    }while( i != ring->idx);

    return NULL;
}

static void hashtable_destroy(gliss_hashtable_t* h)
{
    unsigned int i, j;
    gliss_entry_ring_t** table;

    if( h != NULL )
    {
        table = h->table;
        if( table != NULL )
        {
            for (i = 0; i < h->tablelength; i++)
            {
                if(table[i] != NULL)
                {
                    if(table[i]->entries != NULL){
                        j = table[i]->idx;
                        do{
                            // Erase each instruction
                            free(table[i]->entries[j].value);
                            j = MODULO((j-1), h->tabledepth);
                        }while( j != table[i]->idx);
                        // Erase each entry array of gliss_entry_t
                        free(table[i]->entries);
                    }
                    // Erase each struct gliss_entry_ring_t
                    free(table[i]);
                }
            }
            // Erase the hashtable array of gliss_entry_ring_t*
            free(table);
        }
        // Erase gliss_hashtable_t
        free(h);
    }
}
// END GLISS_FIXED_DECODE_CACHE && !GLISS_LRU_DECODE_CACHE///////////////////////////////////
#endif

#if defined(GLISS_LRU_DECODE_CACHE)

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
        #ifndef GLISS_NO_MALLOC
        init->value = NULL;
        #endif
        for(j = 0; j < (depth-1); ++j)
        {
            tmp1 = h->entry_tab + i*depth +j+1;
            if( tmp1 == NULL)
            {
                hashtable_destroy(h);
                return NULL;
            }
            tmp1->key   = -1;
            #ifndef GLISS_NO_MALLOC
			tmp1->value = NULL;
			#endif

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
                        #ifndef GLISS_NO_MALLOC
                        free(tmp->value);
                        #endif
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

#endif // GLISS_LRU_DECODE_CACHE

/* End of file gliss_decode.c */
