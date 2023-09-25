module core.memory;

struct GC{
	pragma(mangle, "gc_extend") static size_t extend(void* p, size_t mx, size_t sz, const TypeInfo ti = null) pure nothrow;

	private static struct BlkInfo{
		void*  base;
		size_t size;
		uint   attr;
	}
    enum BlkAttr : uint
    {
        NONE        = 0b0000_0000, /// No attributes set.
        FINALIZE    = 0b0000_0001, /// Finalize the data in this block on collect.
        NO_SCAN     = 0b0000_0010, /// Do not scan through this block on collect.
        NO_MOVE     = 0b0000_0100, /// Do not move this memory block on collect.
        APPENDABLE  = 0b0000_1000,
        NO_INTERIOR = 0b0001_0000,
        STRUCTFINAL = 0b0010_0000, // the block has a finalizer for (an array of) structs
    }
	pragma(mangle, "gc_qalloc") static BlkInfo qalloc(size_t sz, uint ba = 0, const scope TypeInfo ti = null) pure nothrow;
}
