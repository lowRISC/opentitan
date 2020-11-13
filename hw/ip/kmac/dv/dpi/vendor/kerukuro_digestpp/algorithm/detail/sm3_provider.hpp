/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_SM3_HPP
#define DIGESTPP_PROVIDERS_SM3_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace sm3_functions
{
	static inline uint32_t xorf(uint32_t x, uint32_t y, uint32_t z)
	{
		return x ^ y ^ z;
	}

	static inline uint32_t ff1(uint32_t x, uint32_t y, uint32_t z)
	{
		return (x & y) ^ (x & z) ^ (y & z);
	}

	static inline uint32_t gg1(uint32_t x, uint32_t y, uint32_t z)
	{
		return (x & y) ^ (~x & z);
	}

	static inline uint32_t p0(uint32_t x)
	{
		return x ^ rotate_left(x, 9) ^ rotate_left(x, 17);
	}

	static inline uint32_t p1(uint32_t x)
	{
		return x ^ rotate_left(x, 15) ^ rotate_left(x, 23);
	}
}

class sm3_provider
{
public:
	static const bool is_xof = false;

	sm3_provider()
	{
	}

	~sm3_provider()
	{
		clear();
	}

	inline void init()
	{
		H[0] = 0x7380166f;
		H[1] = 0x4914b2b9;
		H[2] = 0x172442d7;
		H[3] = 0xda8a0600;
		H[4] = 0xa96f30bc;
		H[5] = 0x163138aa;
		H[6] = 0xe38dee4d;
		H[7] = 0xb0fb0e4e;
		pos = 0;
		total = 0;
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
		if (pos > 56)
		{
			if (pos != 64)
				memset(&m[pos], 0, 64 - pos);
			transform(m.data(), 1);
			pos = 0;
		}
		memset(&m[pos], 0, 56 - pos);
		uint64_t mlen = byteswap(total);
		memcpy(&m[64 - 8], &mlen, 64 / 8);
		transform(m.data(), 1);
		for (int i = 0; i < 8; i++)
			H[i] = byteswap(H[i]);
		memcpy(hash, H.data(), 32);
	}

	inline void clear()
	{
		zero_memory(H);
		zero_memory(m);
	}

	inline size_t hash_size() const { return 256; }

private:
	inline void transform(const unsigned char* data, size_t num_blks)
	{
		for (uint64_t blk = 0; blk < num_blks; blk++)
		{
			uint32_t M[16];
			for (uint32_t i = 0; i < 64 / 4; i++)
				M[i] = byteswap(reinterpret_cast<const uint32_t*>(data)[blk * 16 + i]);

			uint32_t W[68];
			uint32_t W2[64];
			for (int t = 0; t <= 15; t++)
				W[t] = M[t];
			for (int t = 16; t <= 67; t++)
				W[t] = sm3_functions::p1(W[t - 16] ^ W[t - 9] ^ rotate_left(W[t - 3], 15)) ^ rotate_left(W[t - 13], 7) ^ W[t - 6];
			for (int t = 0; t <= 63; t++)
				W2[t] = W[t] ^ W[t + 4];

			uint32_t a = H[0];
			uint32_t b = H[1];
			uint32_t c = H[2];
			uint32_t d = H[3];
			uint32_t e = H[4];
			uint32_t f = H[5];
			uint32_t g = H[6];
			uint32_t h = H[7];

			for (int t = 0; t <= 15; t++)
			{
				uint32_t ss1 = rotate_left((rotate_left(a, 12) + e + rotate_left(0x79cc4519U, t)), 7);
				uint32_t ss2 = ss1 ^ rotate_left(a, 12);
				uint32_t tt1 = sm3_functions::xorf(a, b, c) + d + ss2 + W2[t];
				uint32_t tt2 = sm3_functions::xorf(e, f, g) + h + ss1 + W[t];
				d = c;
				c = rotate_left(b, 9);
				b = a;
				a = tt1;
				h = g;
				g = rotate_left(f, 19);
				f = e;
				e = sm3_functions::p0(tt2);
			}

			for (int t = 16; t <= 63; t++)
			{
				uint32_t ss1 = rotate_left((rotate_left(a, 12) + e + rotate_left(0x7a879d8aU, t)), 7);
				uint32_t ss2 = ss1 ^ rotate_left(a, 12);
				uint32_t tt1 = sm3_functions::ff1(a, b, c) + d + ss2 + W2[t];
				uint32_t tt2 = sm3_functions::gg1(e, f, g) + h + ss1 + W[t];
				d = c;
				c = rotate_left(b, 9);
				b = a;
				a = tt1;
				h = g;
				g = rotate_left(f, 19);
				f = e;
				e = sm3_functions::p0(tt2);
			}

			H[0] ^= a;
			H[1] ^= b;
			H[2] ^= c;
			H[3] ^= d;
			H[4] ^= e;
			H[5] ^= f;
			H[6] ^= g;
			H[7] ^= h;
		}
	}

	std::array<uint32_t, 8> H;
	std::array<unsigned char, 64> m;
	size_t pos;
	uint64_t total;
};

} // namespace detail

} // namespace digestpp

#endif