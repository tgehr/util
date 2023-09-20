module core.errno;

int errno;

void setErrno(int x){ errno=x; }
int getErrno(){ return errno; }
