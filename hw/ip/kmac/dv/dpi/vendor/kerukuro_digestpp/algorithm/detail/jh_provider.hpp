/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_JH_HPP
#define DIGESTPP_PROVIDERS_JH_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/jh_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace jh_functions
{
	static inline void bitswap(uint64_t& x, uint64_t mask, int shift)
	{
		x = ((x & mask) << shift) | ((x & ~mask) >> shift);
	}

	static inline void bitswap(std::array<uint64_t, 16>& H, uint64_t mask, int shift)
	{
		bitswap(H[2], mask, shift);
		bitswap(H[3], mask, shift);
		bitswap(H[6], mask, shift);
		bitswap(H[7], mask, shift);
		bitswap(H[10], mask, shift);
		bitswap(H[11], mask, shift);
		bitswap(H[14], mask, shift);
		bitswap(H[15], mask, shift);
	}

	static inline void Sbitsli(uint64_t& x0a, uint64_t& x0b, uint64_t& x1a, uint64_t& x1b, uint64_t& x2a, uint64_t& x2b,
			uint64_t& x3a, uint64_t& x3b, uint64_t ca, uint64_t cb)
	{
		x3a = ~x3a;
		x3b = ~x3b;
		x0a ^= (ca & ~x2a);
		x0b ^= (cb & ~x2b);
		uint64_t ta = ca ^ (x0a & x1a);
		uint64_t tb = cb ^ (x0b & x1b);
		x0a ^= (x2a & x3a);
		x0b ^= (x2b & x3b);
		x3a ^= (~x1a & x2a);
		x3b ^= (~x1b & x2b);
		x1a ^= (x0a & x2a);
		x1b ^= (x0b & x2b);
		x2a ^= (x0a & ~x3a);
		x2b ^= (x0b & ~x3b);
		x0a ^= (x1a | x3a);
		x0b ^= (x1b | x3b);
		x3a ^= (x1a & x2a);
		x3b ^= (x1b & x2b);
		x1a ^= (ta & x0a);
		x1b ^= (tb & x0b);
		x2a ^= ta;
		x2b ^= tb;
	}

	static inline void Lbitsli(std::array<uint64_t, 16>& H)
	{
		H[2] ^= H[4];
		H[3] ^= H[5];
		H[6] ^= H[8];
		H[7] ^= H[9];
		H[10] ^= H[12] ^ H[0];
		H[11] ^= H[13] ^ H[1];
		H[14] ^= H[0];
		H[15] ^= H[1];
		H[0] ^= H[6];
		H[1] ^= H[7];
		H[4] ^= H[10];
		H[5] ^= H[11];
		H[8] ^= H[14] ^ H[2];
		H[9] ^= H[15] ^ H[3];
		H[12] ^= H[2];
		H[13] ^= H[3];
	}

	static inline void round(std::array<uint64_t, 16>& H, int r, uint64_t mask, int shift)
	{
		jh_functions::Sbitsli(H[0], H[1], H[4], H[5], H[8], H[9], H[12], H[13],
				jh_constants<void>::C[r * 4 + 0], jh_constants<void>::C[r * 4 + 1]);
		jh_functions::Sbitsli(H[2], H[3], H[6], H[7], H[10], H[11], H[14], H[15],
				jh_constants<void>::C[r * 4 + 2], jh_constants<void>::C[r * 4 + 3]);
		jh_functions::Lbitsli(H);
		if (shift)
			jh_functions::bitswap(H, mask, shift);
	}
}

class jh_provider
{
public:
	static const bool is_xof = false;

	jh_provider(size_t hashsize = 512)
		: hs(hashsize)
	{
		validate_hash_size(hashsize, 512);
	}

	~jh_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;

		zero_memory(H);
		H[0] = byteswap(static_cast<uint16_t>(hs));

		unsigned char msg[64];
		memset(msg, 0, sizeof(msg));
		transform(msg, 1);
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, 64, 64, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len); });
	}

	inline void final(unsigned char* hash)
	{
		total += pos * 8;
		m[pos++] = 0x80;
		if (pos > 1)
		{
			if (pos != 64)
				memset(&m[pos], 0, 64 - pos);
			transform(&m[0], 1);
			pos = 0;
		}
		memset(&m[0] + pos, 0, 56 - pos);
		uint64_t mlen = byteswap(total);
		memcpy(&m[0] + (64 - 8), &mlen, 64 / 8);
		transform(&m[0], 1);

		memcpy(hash, reinterpret_cast<unsigned char*>(H.data()) + 128 - hash_size() / 8, hash_size() / 8);
	}

	inline void clear()
	{
		zero_memory(H);
		zero_memory(m);
	}

	inline size_t hash_size() const { return hs; }

private:
	inline void transform(const unsigned char* mp, size_t num_blks)
	{
		for (uint64_t blk = 0; blk < num_blks; blk++)
		{
			const uint64_t* M = (const uint64_t*)(((const unsigned char*)mp) + blk * 64);
			H[0] ^= M[0];
			H[1] ^= M[1];
			H[2] ^= M[2];
			H[3] ^= M[3];
			H[4] ^= M[4];
			H[5] ^= M[5];
			H[6] ^= M[6];
			H[7] ^= M[7];

			// partially unroll
			for (int r = 0; r < 42; r += 7)
			{
				jh_functions::round(H, r, 0x5555555555555555ULL, 1);
				jh_functions::round(H, r + 1, 0x3333333333333333ULL, 2);
				jh_functions::round(H, r + 2, 0x0f0f0f0f0f0f0f0fULL, 4);
				jh_functions::round(H, r + 3, 0x00ff00ff00ff00ffULL, 8);
				jh_functions::round(H, r + 4, 0x0000ffff0000ffffULL, 16);
				jh_functions::round(H, r + 5, 0x00000000ffffffffULL, 32);
				jh_functions::round(H, r + 6, 0, 0);

				std::swap(H[2], H[3]);
				std::swap(H[6], H[7]);
				std::swap(H[10], H[11]);
				std::swap(H[14], H[15]);
			}

			H[8] ^= M[0];
			H[9] ^= M[1];
			H[10] ^= M[2];
			H[11] ^= M[3];
			H[12] ^= M[4];
			H[13] ^= M[5];
			H[14] ^= M[6];
			H[15] ^= M[7];
		}
	}

	std::array<uint64_t, 16> H;
	std::array<unsigned char, 64> m;
	size_t hs;
	size_t pos;
	uint64_t total;
};

} // namespace detail

} // namespace digestpp

#endif