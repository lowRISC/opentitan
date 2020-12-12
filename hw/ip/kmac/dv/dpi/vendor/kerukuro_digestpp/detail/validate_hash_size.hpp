/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_DETAIL_VALIDATE_HASH_SIZE_HPP
#define DIGESTPP_DETAIL_VALIDATE_HASH_SIZE_HPP

namespace digestpp
{
namespace detail
{

// Validate that variable hash is within the list of allowed sizes
inline void validate_hash_size(size_t hs, std::initializer_list<size_t> set)
{
	if (!hs)
		throw std::runtime_error("hash size can't be zero");

	if (std::find(set.begin(), set.end(), hs))
		return;

	throw std::runtime_error("invalid hash size");
}

// Validate variable hash size up to max bits
inline void validate_hash_size(size_t hs, size_t max)
{
	if (!hs)
		throw std::runtime_error("hash size can't be zero");

	if (hs % 8)
		throw std::runtime_error("non-byte hash sizes are not supported");

	if (hs > max)
		throw std::runtime_error("invalid hash size");
}

} // namespace detail
} // namespace digestpp

#endif // DIGESTPP_DETAIL_VALIDATE_HASH_SIZE_HPP