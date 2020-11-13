/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_DETAIL_TRAITS_HPP
#define DIGESTPP_DETAIL_TRAITS_HPP

#include <cstddef> // needed for testing std::byte

namespace digestpp
{
namespace detail
{

template <typename T>
struct is_xof
{
	static const bool value = T::is_xof;
};

template <typename T>
struct is_byte
{
	static const bool value = std::is_same<T, char>::value ||
			std::is_same<T, signed char>::value ||
#if (defined(_HAS_STD_BYTE) && _HAS_STD_BYTE) || (defined(__cpp_lib_byte) && __cpp_lib_byte >= 201603)
			std::is_same<T, std::byte>::value ||
#endif
			std::is_same<T, unsigned char>::value;
};

} // namespace detail
} // namespace digestpp

#endif // DIGESTPP_DETAIL_TRAITS_HPP