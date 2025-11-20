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
		real cbrt(real x);
		real hypot2(real x);
		real hypot3(real x);
		real exp(real x);
		real exp2(real x);
		real expm1(real x);
		real log(real x);
		real log1p(real x);
		real log10(real x);
		real log2(real x);
		real sin(real x);
		real asin(real x);
		real cos(real x);
		real acos(real x);
		real tan(real x);
		real atan(real x);
		real atan2(real y,real x);
		real sinh(real x);
		real asinh(real x);
		real cosh(real x);
		real acosh(real x);
		real tanh(real x);
		real atanh(real x);
		real erf(real x);
		real erfc(real x);
		real tgamma(real x);
		real lgamma(real x);
	}
}else{
	public import std.math;
	public import std.mathspecial;
	alias tgamma=gamma;
	alias lgamma=logGamma;
}
