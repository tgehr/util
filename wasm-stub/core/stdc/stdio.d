module core.stdc.stdio;

extern(C)
pragma(printf)
int snprintf(scope char* s, size_t n, scope const char* fmt, scope const ...);
