/* glibc >=2.38 header redirect compat: aws-lc (libaes_fallback.a) is compiled
   against the system glibc headers which redirect sscanf/strtol to the C23
   symbols __isoc23_*, absent from the (older) Lean toolchain glibc used at link.
   Provide them as plain aliases (ABI-identical; differ only in "0b" parsing).
   No <stdio.h>/<stdlib.h> include -> avoids re-triggering the redirect here. */
typedef __builtin_va_list valist;
extern int vsscanf(const char *, const char *, valist);
extern long strtol(const char *, char **, int);
extern unsigned long strtoul(const char *, char **, int);
extern long long strtoll(const char *, char **, int);
extern unsigned long long strtoull(const char *, char **, int);
int  __isoc23_sscanf(const char *s, const char *f, ...){ valist a; __builtin_va_start(a,f); int r=vsscanf(s,f,a); __builtin_va_end(a); return r; }
long __isoc23_strtol(const char *n, char **e, int b){ return strtol(n,e,b); }
unsigned long __isoc23_strtoul(const char *n, char **e, int b){ return strtoul(n,e,b); }
long long __isoc23_strtoll(const char *n, char **e, int b){ return strtoll(n,e,b); }
unsigned long long __isoc23_strtoull(const char *n, char **e, int b){ return strtoull(n,e,b); }
