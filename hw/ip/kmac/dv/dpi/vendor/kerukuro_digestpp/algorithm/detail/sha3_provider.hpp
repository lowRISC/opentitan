/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_SHA3_HPP
#define DIGESTPP_PROVIDERS_SHA3_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/sha3_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace sha3_functions
{
	template<int R>
	static inline void transform(uint64_t* A)
	{
		for (int round = 24 - R; round < 24; round++)
		{
			uint64_t C[5], D[5];
			C[0] = A[0 * 5 + 0] ^ A[1 * 5 + 0] ^ A[2 * 5 + 0] ^ A[3 * 5 + 0] ^ A[4 * 5 + 0];
			C[1] = A[0 * 5 + 1] ^ A[1 * 5 + 1] ^ A[2 * 5 + 1] ^ A[3 * 5 + 1] ^ A[4 * 5 + 1];
			C[2] = A[0 * 5 + 2] ^ A[1 * 5 + 2] ^ A[2 * 5 + 2] ^ A[3 * 5 + 2] ^ A[4 * 5 + 2];
			C[3] = A[0 * 5 + 3] ^ A[1 * 5 + 3] ^ A[2 * 5 + 3] ^ A[3 * 5 + 3] ^ A[4 * 5 + 3];
			C[4] = A[0 * 5 + 4] ^ A[1 * 5 + 4] ^ A[2 * 5 + 4] ^ A[3 * 5 + 4] ^ A[4 * 5 + 4];

			D[0] = C[4] ^ rotate_left(C[1], 1);
			D[1] = C[0] ^ rotate_left(C[2], 1);
			D[2] = C[1] ^ rotate_left(C[3], 1);
			D[3] = C[2] ^ rotate_left(C[4], 1);
			D[4] = C[3] ^ rotate_left(C[0], 1);

			uint64_t B00 = A[0 * 5 + 0] ^ D[0];
			uint64_t B10 = rotate_left(A[0 * 5 + 1] ^ D[1], 1);
			uint64_t B20 = rotate_left(A[0 * 5 + 2] ^ D[2], 62);
			uint64_t B5 = rotate_left(A[0 * 5 + 3] ^ D[3], 28);
			uint64_t B15 = rotate_left(A[0 * 5 + 4] ^ D[4], 27);

			uint64_t B16 = rotate_left(A[1 * 5 + 0] ^ D[0], 36);
			uint64_t B1 = rotate_left(A[1 * 5 + 1] ^ D[1], 44);
			uint64_t B11 = rotate_left(A[1 * 5 + 2] ^ D[2], 6);
			uint64_t B21 = rotate_left(A[1 * 5 + 3] ^ D[3], 55);
			uint64_t B6 = rotate_left(A[1 * 5 + 4] ^ D[4], 20);

			uint64_t B7 = rotate_left(A[2 * 5 + 0] ^ D[0], 3);
			uint64_t B17 = rotate_left(A[2 * 5 + 1] ^ D[1], 10);
			uint64_t B2 = rotate_left(A[2 * 5 + 2] ^ D[2], 43);
			uint64_t B12 = rotate_left(A[2 * 5 + 3] ^ D[3], 25);
			uint64_t B22 = rotate_left(A[2 * 5 + 4] ^ D[4], 39);

			uint64_t B23 = rotate_left(A[3 * 5 + 0] ^ D[0], 41);
			uint64_t B8 = rotate_left(A[3 * 5 + 1] ^ D[1], 45);
			uint64_t B18 = rotate_left(A[3 * 5 + 2] ^ D[2], 15);
			uint64_t B3 = rotate_left(A[3 * 5 + 3] ^ D[3], 21);
			uint64_t B13 = rotate_left(A[3 * 5 + 4] ^ D[4], 8);

			uint64_t B14 = rotate_left(A[4 * 5 + 0] ^ D[0], 18);
			uint64_t B24 = rotate_left(A[4 * 5 + 1] ^ D[1], 2);
			uint64_t B9 = rotate_left(A[4 * 5 + 2] ^ D[2], 61);
			uint64_t B19 = rotate_left(A[4 * 5 + 3] ^ D[3], 56);
			uint64_t B4 = rotate_left(A[4 * 5 + 4] ^ D[4], 14);

			A[0 * 5 + 0] = B00 ^ ((~B1) & B2);
			A[0 * 5 + 1] = B1 ^ ((~B2) & B3);
			A[0 * 5 + 2] = B2 ^ ((~B3) & B4);
			A[0 * 5 + 3] = B3 ^ ((~B4) & B00);
			A[0 * 5 + 4] = B4 ^ ((~B00) & B1);

			A[1 * 5 + 0] = B5 ^ ((~B6) & B7);
			A[1 * 5 + 1] = B6 ^ ((~B7) & B8);
			A[1 * 5 + 2] = B7 ^ ((~B8) & B9);
			A[1 * 5 + 3] = B8 ^ ((~B9) & B5);
			A[1 * 5 + 4] = B9 ^ ((~B5) & B6);

			A[2 * 5 + 0] = B10 ^ ((~B11) & B12);
			A[2 * 5 + 1] = B11 ^ ((~B12) & B13);
			A[2 * 5 + 2] = B12 ^ ((~B13) & B14);
			A[2 * 5 + 3] = B13 ^ ((~B14) & B10);
			A[2 * 5 + 4] = B14 ^ ((~B10) & B11);

			A[3 * 5 + 0] = B15 ^ ((~B16) & B17);
			A[3 * 5 + 1] = B16 ^ ((~B17) & B18);
			A[3 * 5 + 2] = B17 ^ ((~B18) & B19);
			A[3 * 5 + 3] = B18 ^ ((~B19) & B15);
			A[3 * 5 + 4] = B19 ^ ((~B15) & B16);

			A[4 * 5 + 0] = B20 ^ ((~B21) & B22);
			A[4 * 5 + 1] = B21 ^ ((~B22) & B23);
			A[4 * 5 + 2] = B22 ^ ((~B23) & B24);
			A[4 * 5 + 3] = B23 ^ ((~B24) & B20);
			A[4 * 5 + 4] = B24 ^ ((~B20) & B21);

			A[0] ^= sha3_constants<void>::RC[round];
		}
	}

	template<int R>
	static inline void transform(const unsigned char* data, uint64_t num_blks, uint64_t* A, size_t rate)
	{
		size_t r = rate / 8;
		size_t r64 = rate / 64;
		for (uint64_t blk = 0; blk < num_blks; blk++)
		{
			for (size_t i = 0; i < r64; i++)
				A[i] ^= reinterpret_cast<const uint64_t*>(data+blk*r)[i];

			transform<R>(A);
		}
	}

} // namespace sha3_functions


class sha3_provider
{
public:
	static const bool is_xof = false;

	sha3_provider(size_t hashsize)
		: hs(hashsize)
	{
		validate_hash_size(hashsize, {224, 256, 384, 512});
		rate = 1600U - hs * 2;
	}

	~sha3_provider()
	{
		clear();
	}

	inline void init()
	{
		zero_memory(A);
		pos = 0;
		total = 0;
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, rate / 8, rate / 8, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { sha3_functions::transform<24>(data, len, A.data(), rate); });
	}

	inline void final(unsigned char* hash)
	{
		size_t r = rate / 8;
		m[pos++] = 0x06;
		if (r != pos)
			memset(&m[pos], 0, r - pos);
		m[r - 1] |= 0x80;
		sha3_functions::transform<24>(m.data(), 1, A.data(), rate);
		memcpy(hash, A.data(), hash_size() / 8);
	}

	inline size_t hash_size() const
	{
		return hs;
	}

	inline void clear()
	{
		zero_memory(A);
		zero_memory(m);
	}

private:
	std::array<uint64_t, 25> A;
	std::array<unsigned char, 144> m;
	size_t pos;
	size_t hs;
	size_t rate;
	uint64_t total;
};

} // namespace detail

} // namespace digestpp

#endif // DIGESTPP_PROVIDERS_SHA3_HPP
