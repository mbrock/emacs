/* comphack.h - Minimal definitions for compiling generated .eln C code */

#ifndef COMPHACK_H
#define COMPHACK_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* Basic Lisp_Object type - just a tagged pointer/integer */
typedef intptr_t Lisp_Object;

/* Basic constants - using low integers as tags */
#define Qnil ((Lisp_Object)0)
#define Qt ((Lisp_Object)1)
#define Qmany ((Lisp_Object)2)
#define CONST Qnil  /* Placeholder for constants */

/* Thread state - minimal definition */
struct thread_state {
    void *dummy;  /* Just a placeholder */
};

/* Static object type for serialized data */
typedef struct {
    ptrdiff_t len;
    char data[];  /* Flexible array member */
} static_obj_t;

/* The freloc_link_table struct is defined in generated code */
struct freloc_link_table;

/* Fixnum operations */
#define FIXNUM_BITS (sizeof(Lisp_Object) * 8 - 3)

static inline Lisp_Object make_fixnum(intptr_t n) {
    return (n << 2) | 2;  /* Tag with 10 in low bits */
}

static inline intptr_t XFIXNUM(Lisp_Object a) {
    return a >> 2;
}

/* String creation stubs */
static inline Lisp_Object build_string(const char *str) {
    (void)str;
    return Qnil;  /* Stub */
}

static inline Lisp_Object intern_c_string(const char *str) {
    (void)str;
    return Qnil;  /* Stub */
}

/* Compiler intrinsic stubs */
static inline Lisp_Object comp_maybe_gc_or_quit(ptrdiff_t n, Lisp_Object *args) {
    (void)n; (void)args;
    return Qnil;  /* No-op stub */
}

/* Cons cell stub */
static inline Lisp_Object Fcons(Lisp_Object car, Lisp_Object cdr) {
    (void)car; (void)cdr;
    return Qnil;  /* Stub */
}

/* Comp unit structure - minimal */
struct Lisp_Native_Comp_Unit {
    Lisp_Object header;
    /* Other fields we don't need for now */
};

/* Define these to satisfy generated code */
#define config_h 1
#define lisp_h 1
#define comp_h 1

/* Code generation macros */
#define CALL(f, ...) (fn->f (__VA_ARGS__))
#define RELOC(i) d_reloc[i]
#define RELOC_IMP(i) d_reloc_imp[i]
#define RELOC_EPH(i) d_reloc_eph[i]
#define LIST(...) (Lisp_Object[]){__VA_ARGS__}

#define DEFBLOB(name, str)                                              \
  struct { ptrdiff_t len; char data[sizeof(str)]; } name ## _blob =     \
    { .len = sizeof(str), .data = str };                                \
  static static_obj_t *name = (static_obj_t *)&name ## _blob

#define REGISTER_SUBR(name_idx, cname_idx, min, max, rest_idx)  \
  fn->f_comp__register_subr(RELOC_EPH(name_idx), RELOC_EPH(cname_idx),  \
                            make_fixnum(min), make_fixnum(max),           \
                            Qnil, RELOC_EPH(rest_idx), comp_u)

#define ARGS_0    (void)
#define ARGS_1    (Lisp_Object arg0)
#define ARGS_2    (Lisp_Object arg0, Lisp_Object arg1)
#define ARGS_3    (Lisp_Object arg0, Lisp_Object arg1, Lisp_Object arg2)
#define ARGS_MANY (ptrdiff_t nargs, Lisp_Object *args)

#define DEFUN(lisp_name, c_name, args) \
  /* lisp_name */ \
  Lisp_Object c_name args

#endif /* COMPHACK_H */