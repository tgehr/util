module util.float_;
// hacky float formatter (TODO: replace with dedicated algorithm)
import core.stdc.stdio,core.stdc.float_,std.conv,std.math,std.complex,std.traits;
enum int maxDigits10(T)=cast(int)ceil(T.mant_dig*log10(double(FLT_RADIX)))+5;
bool containsDotOrExp(scope const string s){
	foreach(ch; s)
        if(ch=='.'||ch=='e'||ch=='E')
	        return true;
    return false;
}
bool roundTrips(T)(scope const string s,T x)if(isFloatingPoint!T){
    try{
	    auto t=cast()s;
        return parse!T(t)==x;
    }catch (ConvException){
        return false;
    }
}
string normalizeExponent(T)(string s, T x)if(isFloatingPoint!T){
    size_t epos=size_t.max;
    foreach(i,ch;s) if(ch=='e'||ch=='E'){epos=i;break;}
    if(epos==size_t.max) return s;
    auto mant=s[0..epos],exp=s[epos+1..$],esign='+';
    size_t j=0;
    if(exp.length&&(exp[0]=='+'||exp[0]=='-')) esign=exp[0],j=1;
    for(;j<exp.length&&exp[j]=='0';++j){}
    auto digits=j<exp.length?exp[j..$]:"0";
    auto candidate=mant~(esign=='-'?"e-":"e")~digits;
    return roundTrips!T(candidate,x)?candidate:s;
}
string snprintfG(T)(T x,int prec)if(isFloatingPoint!T){
	char[64] sbuf;
    for(size_t cap=64;;cap*=2){
	    auto buf=cap==64?sbuf[]:new char[](cap);
        static if(is(T==real)){
	        static assert(T.sizeof==16);
	        auto n=snprintf(buf.ptr,buf.length,"%.*Lg",prec,x);
        }else auto n=snprintf(buf.ptr,buf.length,"%.*g",prec,cast(double)x);
        if(n>=0&&cast(size_t)n<buf.length)
            return buf[0..cast(size_t)n].idup;
    }
}
string snprintfHex(T)(T x)if(isFloatingPoint!T){
	char[64] sbuf;
	for(size_t cap=64;;cap*=2){
	    auto buf=cap==64?sbuf[]:new char[](cap);
        static if(is(T==real)) auto n=snprintf(buf.ptr,buf.length,"%La",x);
        else auto n=snprintf(buf.ptr,buf.length,"%a",cast(double)x);
        if(n>=0&&cast(size_t)n<buf.length)
            return buf[0..cast(size_t)n].idup;
    }
}
string toStringRT(T)(T x,bool pythonStyle=true)if(isFloatingPoint!T){
    if(isNaN(x)) return "nan";
    if(isInfinity(x)) return signbit(x)?"-inf":"inf";
    if(x==0){
        if(signbit(x)) return pythonStyle?"-0.0":"-0";
        return pythonStyle?"0.0" :"0";
    }
    enum int maxP=maxDigits10!T;
    foreach(p;1..maxP+1){
        auto s=snprintfG!T(x,p);
        s=normalizeExponent!T(s,x);
        if(pythonStyle&&!containsDotOrExp(s)){
	        auto withDot=s~".0";
            if(roundTrips!T(withDot,x))
	            s=withDot;
        }
        if(roundTrips!T(s,x))
            return s;
    }
    return snprintfHex!T(x);
}
string toStringRT(T)(Complex!T x,bool pythonStyle=false)if(isFloatingPoint!T){
	if(x.re!=0) return toStringRT(x.re,pythonStyle)~"+"~toStringRT(x.im,pythonStyle)~"i";
	return toStringRT(x.im,pythonStyle)~"i";
}
