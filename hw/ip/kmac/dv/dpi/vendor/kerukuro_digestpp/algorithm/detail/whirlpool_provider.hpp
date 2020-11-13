/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_WHIRLPOOL_HPP
#define DIGESTPP_PROVIDERS_WHIRLPOOL_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "constants/whirlpool_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace whirlpool_functions
{
	template<int a>
	static inline uint64_t G(const uint64_t* ll)
	{
			return whirlpool_constants<void>::T[0][static_cast<unsigned char>(ll[a % 8])]
				^ whirlpool_constants<void>::T[1][static_cast<unsigned char>(ll[(a - 1) % 8] >> 8)]
				^ whirlpool_constants<void>::T[2][static_cast<unsigned char>(ll[(a - 2) % 8] >> 16)]
				^ whirlpool_constants<void>::T[3][static_cast<unsigned char>(ll[(a - 3) % 8] >> 24)]
				^ whirlpool_constants<void>::T[4][static_cast<unsigned char>(ll[(a - 4) % 8] >> 32)]
				^ whirlpool_constants<void>::T[5][static_cast<unsigned char>(ll[(a - 5) % 8] >> 40)]
				^ whirlpool_constants<void>::T[6][static_cast<unsigned char>(ll[(a - 6) % 8] >> 48)]
				^ whirlpool_constants<void>::T[7][static_cast<unsigned char>(ll[(a - 7) % 8] >> 56)];
	}
}

class whirlpool_provider
{
public:
	static const bool is_xof = false;

	whirlpool_provider()
	{
	}

	~whirlpool_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;
		memset(&h[0], 0, sizeof(uint64_t)*8);
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, 64, 64, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len); });
	}

	inline void final(unsigned char* hash)
	{
		total += pos * 8;
		uint64_t mlen = byteswap(total);
		m[pos++] = 0x80;
		if (pos > 32)
		{
			if (pos != 64)
				memset(&m[pos], 0, 64 - pos);
			transform(m.data(), 1);
			pos = 0;
		}
		memset(&m[pos], 0, 56 - pos);
		memcpy(&m[64 - 8], &mlen, 64 / 8);
		transform(m.data(), 1);
		memcpy(hash, h.data(), hash_size() / 8);
	}

	inline void clear()
	{
		zero_memory(h);
		zero_memory(m);
	}

	inline size_t hash_size() const { return 512; }

private:
	inline void transform(const unsigned char* mp, size_t num_blks)
	{
		for (uint64_t b = 0; b < num_blks; b++)
		{
			uint64_t K[8], state[8];

			memcpy(K, h.data(), sizeof(K));
			for (int i = 0; i < 8; ++i)
				state[i] = h[i] ^ (reinterpret_cast<const uint64_t*>(mp)[i]);

			for (int r = 0; r < 10; ++r)
			{
				uint64_t L[8];

				L[0] = whirlpool_functions::G<0 + 8>(K) ^ whirlpool_constants<void>::RC[r];
				L[1] = whirlpool_functions::G<1 + 8>(K);
				L[2] = whirlpool_functions::G<2 + 8>(K);
				L[3] = whirlpool_functions::G<3 + 8>(K);
				L[4] = whirlpool_functions::G<4 + 8>(K);
				L[5] = whirlpool_functions::G<5 + 8>(K);
				L[6] = whirlpool_functions::G<6 + 8>(K);
				L[7] = whirlpool_functions::G<7 + 8>(K);

				memcpy(K, L, sizeof(L));

				L[0] ^= whirlpool_functions::G<0 + 8>(state);
				L[1] ^= whirlpool_functions::G<1 + 8>(state);
				L[2] ^= whirlpool_functions::G<2 + 8>(state);
				L[3] ^= whirlpool_functions::G<3 + 8>(state);
				L[4] ^= whirlpool_functions::G<4 + 8>(state);
				L[5] ^= whirlpool_functions::G<5 + 8>(state);
				L[6] ^= whirlpool_functions::G<6 + 8>(state);
				L[7] ^= whirlpool_functions::G<7 + 8>(state);

				memcpy(state, L, sizeof(L));
			}

			for (int i = 0; i < 8; ++i)
				h[i] ^= state[i] ^ reinterpret_cast<const uint64_t*>(mp)[i];
			mp += 64;
		}
	}

	std::array<uint64_t, 8> h;
	std::array<unsigned char, 64> m;
	size_t pos;
	uint64_t total;

};

} // namespace detail

} // namespace digestpp

#endif