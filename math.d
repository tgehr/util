module util.math;

version(WASM){
	enum real PI = 0x1.921fb54442d18469898cc51701b84p+1L;
	real abs(real x){ return x<0?-x:x; }
	extern(C){
		real sqrt(real x){
			real r=x;
			foreach(_;0..200)
				r=0.5L*(r+x/r);
			assert(abs(r*r-x)<1e-16);
			return r;
		}
		real sin(real x);
		real asin(real x);
		real cos(real x);
		real acos(real x);
		real tan(real x);
		real atan(real x);
		real exp(real x);
		real log(real x);
	}
}else public import std.math;
