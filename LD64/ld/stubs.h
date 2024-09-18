typedef long off_t;
typedef unsigned int pid_t;
typedef unsigned int mode_t;

#undef va_start
#undef va_end
#undef va_list
typedef __builtin_va_list va_list;
#define va_start(ap, param) __builtin_va_start(ap, param)
#define va_end(ap)          __builtin_va_end(ap)

// This is #if 0'd out in win_fcntl.h
#define F_GETPATH       50              /* return the full path of the fd */


typedef void * caddr_t;
#ifdef __DARWIN_ALIAS_C
#undef __DARWIN_ALIAS_C
#endif
#define __DARWIN_ALIAS_C(a)

#define __API_AVAILABLE(...)
#define __API_UNAVAILABLE(...)
#define __OSX_DEPRECATED(...) 
#define API_DEPRECATED(...) 
#define API_AVAILABLE(...) 
#define API_DEPRECATED_WITH_REPLACEMENT(...)