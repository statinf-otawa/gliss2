/* Generated by gep ($(date)) copyright (c) 2008 IRIT - UPS */
#ifndef GLISS_$(PROC)_INCLUDE_$(PROC)_ID_H
#define GLISS_$(PROC)_INCLUDE_$(PROC)_ID_H

#define $(PROC)_INSTRUCTIONS_NB $(total_instruction_count)

/* ($(proc)_ident_t enumeration */
typedef enum $(proc)_ident_t {
	$(PROC)_UNKNOWN = 0$(foreach instructions),
	$(PROC)_$(IDENT) = $(ICODE)$(end)
} $(proc)_ident_t;

#endif /* GLISS_$(PROC)_INCLUDE_$(PROC)_ID_H */
