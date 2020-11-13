/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_SHA1_HPP
#define DIGESTPP_PROVIDERS_SHA1_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "constants/sha1_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace sha1_functions
{
	static inline uint32_t Ch(uint32_t x, uint32_t y, uint32_t z)
	{
		return (x & y) ^ (~x & z);
	}

	static inline uint32_t Parity(uint32_t x, uint32_t y, uint32_t z)
	{
		return x ^ y ^ z;
	}

	static inline uint32_t Maj(uint32_t x, uint32_t y, uint32_t z)
	{
		return (x & y) ^ (x & z) ^ (y & z);
	}
}

class sha1_provider
{
public:
	static const bool is_xof = false;

	sha1_provider()
	{
	}

	~sha1_provider()
	{
		clear();
	}

	inline void init()
	{
		H[0] = 0x67452301;
		H[1] = 0xefcdab89;
		H[2] = 0x98badcfe;
		H[3] = 0x10325476;
		H[4] = 0xc3d2e1f0;
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
		if (pos > 56) {
			if (pos != 64)
				memset(&m[pos], 0, 64 - pos);
			transform(&m[0], 1);
			pos = 0;
		}
		memset(&m[0] + pos, 0, 56 - pos);
		uint64_t mlen = byteswap(total);
		memcpy(&m[0] + (64 - 8), &mlen, 64 / 8);
		transform(&m[0], 1);
		for (int i = 0; i < 5; i++)
			H[i] = byteswap(H[i]);
		memcpy(hash, H.data(), 160/8);
	}

	inline void clear()
	{
		zero_memory(H);
		zero_memory(m);
	}

	inline size_t hash_size() const { return 160; }

private:
	inline void transform(const unsigned char* data, size_t num_blks)
	{
		for (uint64_t blk = 0; blk < num_blks; blk++)
		{
			uint32_t M[16];
			for (uint32_t i = 0; i < 64 / 4; i++)
				M[i] = byteswap((reinterpret_cast<const uint32_t*>(data)[blk * 16 + i]));

			uint32_t W[80];
			for (int t = 0; t <= 15; t++)
				W[t] = M[t];
			for (int t = 16; t <= 79; t++)
				W[t] = rotate_left(W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16], 1);

			uint32_t a = H[0];
			uint32_t b = H[1];
			uint32_t c = H[2];
			uint32_t d = H[3];
			uint32_t e = H[4];

			uint32_t K = sha1_constants<void>::K[0];
			auto f = sha1_functions::Ch;
			for (int t = 0; t <= 79; t++)
			{
				uint32_t T = rotate_left(a, 5) + f(b, c, d) + e + K + W[t];
				e = d;
				d = c;
				c = rotate_left(b, 30);
				b = a;
				a = T;

				if (t == 19)
				{
					f = sha1_functions::Parity;
					K = sha1_constants<void>::K[1];
				}
				else if (t == 39)
				{
					f = sha1_functions::Maj;
					K = sha1_constants<void>::K[2];
				}
				else if (t == 59)
				{
					f = sha1_functions::Parity;
					K = sha1_constants<void>::K[3];
				}

			}
			H[0] += a;
			H[1] += b;
			H[2] += c;
			H[3] += d;
			H[4] += e;
		}
	}

	std::array<uint32_t, 5> H;
	std::array<unsigned char, 64> m;
	size_t pos;
	uint64_t total;
};

} // namespace detail

} // namespace digestpp

#endif