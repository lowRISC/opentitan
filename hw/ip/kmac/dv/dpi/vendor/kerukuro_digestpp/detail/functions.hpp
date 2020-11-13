/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_DETAIL_FUNCTIONS_HPP
#define DIGESTPP_DETAIL_FUNCTIONS_HPP

namespace digestpp
{
namespace detail
{

// Byte-swap a 16-bit unsigned integer.
inline uint16_t byteswap(uint16_t val)
{
    return ((val & 0xff) << 8) | ((val & 0xff00) >> 8);
}

// Byte-swap a 32-bit unsigned integer.
inline uint32_t byteswap(uint32_t val)
{
    return (((val & 0xff000000) >> 24) |
			((val & 0x00ff0000) >> 8) |
			((val & 0x0000ff00) << 8) |
			((val & 0x000000ff) << 24));
}

// Byte-swap a 64-bit unsigned integer.
inline uint64_t byteswap(uint64_t val)
{
    return (((val & 0xff00000000000000ull) >> 56) |
			((val & 0x00ff000000000000ull) >> 40) |
			((val & 0x0000ff0000000000ull) >> 24) |
			((val & 0x000000ff00000000ull) >> 8) |
			((val & 0x00000000ff000000ull) << 8) |
			((val & 0x0000000000ff0000ull) << 24) |
			((val & 0x000000000000ff00ull) << 40) |
			((val & 0x00000000000000ffull) << 56));
}

#ifdef __APPLE__
inline size_t byteswap(size_t val)
{
	switch(sizeof(size_t))
	{
		case sizeof(uint16_t):
			return (size_t)byteswap((uint16_t)val);

		case sizeof(uint32_t):
			return (size_t)byteswap((uint32_t)val);

		case sizeof(uint64_t):
			return (size_t)byteswap((uint64_t)val);
	}
}
#endif

// Rotate 32-bit unsigned integer to the right.
inline uint32_t rotate_right(uint32_t x, unsigned n)
{
	return (x >> n) | (x << (32 - n));
}

// Rotate 32-bit unsigned integer to the left.
inline uint32_t rotate_left(uint32_t x, unsigned n)
{
	return (x << n) | (x >> (32 - n));
}

// Rotate 64-bit unsigned integer to the right.
inline uint64_t rotate_right(uint64_t x, unsigned n)
{
	return (x >> n) | (x << (64 - n));
}

// Rotate 64-bit unsigned integer to the left.
inline uint64_t rotate_left(uint64_t x, unsigned n)
{
	return (x << n) | (x >> (64 - n));
}

// Clear memory, suppressing compiler optimizations.
inline void zero_memory(void *v, size_t n) {
	volatile unsigned char *p = static_cast<volatile unsigned char *>(v);
	while (n--) {
		*p++ = 0;
	}
}

// Clear memory occupied by an array, suppressing compiler optimizations.
template<typename T, size_t N>
inline void zero_memory(std::array<T, N>& ar)
{
	zero_memory(ar.data(), ar.size() * sizeof(T));
}

// Clear memory occupied by std::string
inline void zero_memory(std::string& s)
{
	if (!s.empty())
		zero_memory(&s[0], s.size());
}


} // namespace detail
} // namespace digestpp

#endif