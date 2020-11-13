/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_BLAKE2_CONSTANTS_HPP
#define DIGESTPP_PROVIDERS_BLAKE2_CONSTANTS_HPP

namespace digestpp
{

namespace detail
{

template<typename T>
struct blake2b_constants
{
	const static uint64_t IV[8];
};

template<typename T>
const uint64_t blake2b_constants<T>::IV[8] = {
	0x6A09E667F3BCC908ull, 0xBB67AE8584CAA73Bull, 0x3C6EF372FE94F82Bull, 0xA54FF53A5F1D36F1ull,
	0x510E527FADE682D1ull, 0x9B05688C2B3E6C1Full, 0x1F83D9ABFB41BD6Bull, 0x5BE0CD19137E2179ull
};

template<typename T>
struct blake2s_constants
{
	const static uint32_t IV[8];
};

template<typename T>
const uint32_t blake2s_constants<T>::IV[8] = {
	0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

template<typename T>
struct blake2_constants
{
	static const uint32_t S[12][16];

};

template<typename T>
const uint32_t blake2_constants<T>::S[12][16] = {
	{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
	{ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
	{ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
	{ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
	{ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
	{ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
	{ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
	{ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
	{ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
	{ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 },
	{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
	{ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 }
};

enum class blake2_type
{
	hash,
	x_hash,
	xof
};

} // namespace detail

} // namespace digestpp

#endif