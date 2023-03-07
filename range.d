module util.range;

import std.range; // TODO: implement from scratch
import util.tuple:tuple;
struct Wrap(T){ T payload; }

struct Zip(R...){
	R ranges;
	@property front(){
		pragma(inline,true)
		auto impl(size_t i)(){
			static if(i<ranges.length){
				return tuple(ranges[i].front,impl!(i+1).expand);
			}else return tuple();
		}
		return impl!0();
	}
	@property bool empty(){
		foreach(ref r;ranges) if(r.empty) return true;
		return false;
	}
	void popFront(){
		foreach(ref r;ranges)
			r.popFront();
	}
}

auto zip(R...)(R ranges){
	return Zip!R(ranges);
}
