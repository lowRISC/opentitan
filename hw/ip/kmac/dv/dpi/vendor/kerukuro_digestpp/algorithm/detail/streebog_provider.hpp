/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_STREEBOG_HPP
#define DIGESTPP_PROVIDERS_STREEBOG_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/streebog_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace streebog_functions
{
	template<int I>
	static inline uint64_t lps(unsigned char* ch)
	{
		return streebog_constants<void>::T[0][(ch[I])]
			^ streebog_constants<void>::T[1][(ch[8 + I])]
			^ streebog_constants<void>::T[2][(ch[16 + I])]
			^ streebog_constants<void>::T[3][(ch[24 + I])]
			^ streebog_constants<void>::T[4][(ch[32 + I])]
			^ streebog_constants<void>::T[5][(ch[40 + I])]
			^ streebog_constants<void>::T[6][(ch[48 + I])]
			^ streebog_constants<void>::T[7][(ch[56 + I])];
	}

	static inline void lps_block(uint64_t* block)
	{
		unsigned char ch[64];
		memcpy(ch, block, 64);

		block[0] = lps<0>(ch);
		block[1] = lps<1>(ch);
		block[2] = lps<2>(ch);
		block[3] = lps<3>(ch);
		block[4] = lps<4>(ch);
		block[5] = lps<5>(ch);
		block[6] = lps<6>(ch);
		block[7] = lps<7>(ch);
	}

	static inline void xor_blocks(uint64_t* block, const uint64_t* toxor)
	{
		block[0] ^= toxor[0];
		block[1] ^= toxor[1];
		block[2] ^= toxor[2];
		block[3] ^= toxor[3];
		block[4] ^= toxor[4];
		block[5] ^= toxor[5];
		block[6] ^= toxor[6];
		block[7] ^= toxor[7];
	}

	static inline void e(uint64_t* K, const unsigned char* m)
	{
		uint64_t tmp[8];
		memcpy(tmp, K, 64);
		xor_blocks(K, reinterpret_cast<const uint64_t*>(m));
		for (int i = 0; i < 12; i++)
		{
			lps_block(K);
			xor_blocks(tmp, &streebog_constants<void>::RC[i][0]);
			lps_block(tmp);
			xor_blocks(K, tmp);
		}
	}

	static inline void gN(uint64_t* h, const unsigned char* m, uint64_t N)
	{
		uint64_t hN[8];
		memcpy(hN, h, 64);
		hN[0] ^= N;
		lps_block(hN);
		e(hN, m);
		xor_blocks(h, hN);
		xor_blocks(h, reinterpret_cast<const uint64_t*>(m));
	}

	static inline void addm(const unsigned char* m, uint64_t* h)
	{
		const uint64_t* m64 = reinterpret_cast<const uint64_t*>(m);
		bool carry = false, overflow = false;
		for (int i = 0; i < 8; i++)
		{
			uint64_t t = h[i] + m64[i];
			overflow = t < h[i] || t < m64[i];
			h[i] = t + carry;
			carry = overflow;
		}
	}

}

class streebog_provider
{
public:
	static const bool is_xof = false;

	streebog_provider(size_t hashsize)
		: hs(hashsize)
	{
		validate_hash_size(hashsize, { 256, 512 });
	}

	~streebog_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;
		memset(&h[0], hs == 512 ? 0 : 1, sizeof(uint64_t) * 8);
		memset(&S[0], 0, sizeof(uint64_t) * 8);
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, 64, 64, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len, false); });
	}

	inline void final(unsigned char* hash)
	{
		m[pos++] = 0x01;
		if (pos != 64)
			memset(&m[pos], 0, 64 - pos);
		transform(&m[0], 1, false);
		total += (pos - 1) * 8;

		memcpy(&m[0], &total, sizeof(total));
		memset(&m[sizeof(total)], 0, 64 - sizeof(total));
		transform(&m[0], 1, true);
		transform(reinterpret_cast<const unsigned char*>(&S[0]), 1, true);

		memcpy(hash, &h[8 - hash_size()/64], hash_size() / 8);
	}

	inline void clear()
	{
		zero_memory(h);
		zero_memory(S);
		zero_memory(m);
	}

	inline size_t hash_size() const { return hs; }

private:
	inline void transform(const unsigned char* mp, size_t num_blks, bool final)
	{
		for (size_t blk = 0; blk < num_blks; blk++)
		{
			streebog_functions::gN(&h[0], mp + blk * 64, final ? 0ULL : total + blk * 512);

			if (!final)
				streebog_functions::addm(mp + blk * 64, &S[0]);
		}
	}

	std::array<uint64_t, 8> h;
	std::array<uint64_t, 8> S;
	std::array<unsigned char, 64> m;
	size_t hs;
	size_t pos;
	uint64_t total;

};

} // namespace detail

} // namespace digestpp

#endif