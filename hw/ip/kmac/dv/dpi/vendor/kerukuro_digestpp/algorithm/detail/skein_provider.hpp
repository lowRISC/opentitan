/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_SKEIN_HPP
#define DIGESTPP_PROVIDERS_SKEIN_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/skein_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

template<size_t N>
struct skein_functions
{
};

template<>
struct skein_functions<4>
{
	template<size_t r> static inline void GTv4(uint64_t* G)
	{
		G[skein_constants<void>::I4[r][0]] += G[skein_constants<void>::I4[r][1]];
		G[skein_constants<void>::I4[r][1]] = rotate_left(G[skein_constants<void>::I4[r][1]],
				skein_constants<void>::C4[r][0]) ^ G[skein_constants<void>::I4[r][0]];
		G[skein_constants<void>::I4[r][2]] += G[skein_constants<void>::I4[r][3]];
		G[skein_constants<void>::I4[r][3]] = rotate_left(G[skein_constants<void>::I4[r][3]],
				skein_constants<void>::C4[r][1]) ^ G[skein_constants<void>::I4[r][2]];
	}

	template<size_t r>
	static inline void KStRv4(uint64_t* G, uint64_t* keys, uint64_t* tweaks)
	{
		G[0] += keys[(r + 0 + 1) % 5];
		G[1] += keys[(r + 1 + 1) % 5] + tweaks[(r + 1) % 3];
		G[2] += keys[(r + 2 + 1) % 5] + tweaks[(r + 2) % 3];
		G[3] += keys[(r + 3 + 1) % 5] + r + 1;
	}

	template<size_t r>
	static inline void G8(uint64_t* G, uint64_t* keys, uint64_t* tweaks)
	{
		GTv4<0>(G);
		GTv4<1>(G);
		GTv4<2>(G);
		GTv4<3>(G);
		KStRv4<r>(G, keys, tweaks);
		GTv4<4>(G);
		GTv4<5>(G);
		GTv4<6>(G);
		GTv4<7>(G);
		KStRv4<r + 1>(G, keys, tweaks);
	}
};

template<>
struct skein_functions<8>
{
	template<size_t r> static inline void GTv4(uint64_t* G)
	{
		G[skein_constants<void>::I8[r][0]] += G[skein_constants<void>::I8[r][1]];
		G[skein_constants<void>::I8[r][1]] = rotate_left(G[skein_constants<void>::I8[r][1]],
				skein_constants<void>::C8[r][0]) ^ G[skein_constants<void>::I8[r][0]];
		G[skein_constants<void>::I8[r][2]] += G[skein_constants<void>::I8[r][3]];
		G[skein_constants<void>::I8[r][3]] = rotate_left(G[skein_constants<void>::I8[r][3]],
				skein_constants<void>::C8[r][1]) ^ G[skein_constants<void>::I8[r][2]];
		G[skein_constants<void>::I8[r][4]] += G[skein_constants<void>::I8[r][5]];
		G[skein_constants<void>::I8[r][5]] = rotate_left(G[skein_constants<void>::I8[r][5]],
				skein_constants<void>::C8[r][2]) ^ G[skein_constants<void>::I8[r][4]];
		G[skein_constants<void>::I8[r][6]] += G[skein_constants<void>::I8[r][7]];
		G[skein_constants<void>::I8[r][7]] = rotate_left(G[skein_constants<void>::I8[r][7]],
				skein_constants<void>::C8[r][3]) ^ G[skein_constants<void>::I8[r][6]];
	}

	template<size_t r>
	static inline void KStRv4(uint64_t* G, uint64_t* keys, uint64_t* tweaks)
	{
		G[0] += keys[(r + 0 + 1) % 9];
		G[1] += keys[(r + 1 + 1) % 9];
		G[2] += keys[(r + 2 + 1) % 9];
		G[3] += keys[(r + 3 + 1) % 9];
		G[4] += keys[(r + 4 + 1) % 9];
		G[5] += keys[(r + 5 + 1) % 9] + tweaks[(r + 1) % 3];
		G[6] += keys[(r + 6 + 1) % 9] + tweaks[(r + 2) % 3];
		G[7] += keys[(r + 7 + 1) % 9] + r + 1;
	}

	template<size_t r>
	static inline void G8(uint64_t* G, uint64_t* keys, uint64_t* tweaks)
	{
		GTv4<0>(G);
		GTv4<1>(G);
		GTv4<2>(G);
		GTv4<3>(G);
		KStRv4<r>(G, keys, tweaks);
		GTv4<4>(G);
		GTv4<5>(G);
		GTv4<6>(G);
		GTv4<7>(G);
		KStRv4<r + 1>(G, keys, tweaks);
	}
};

template<>
struct skein_functions<16>
{

	template<size_t r> static inline void GTv4(uint64_t* G)
	{
		G[skein_constants<void>::I16[r][0]] += G[skein_constants<void>::I16[r][1]];
		G[skein_constants<void>::I16[r][1]] = rotate_left(G[skein_constants<void>::I16[r][1]],
				skein_constants<void>::C16[r][0]) ^ G[skein_constants<void>::I16[r][0]];
		G[skein_constants<void>::I16[r][2]] += G[skein_constants<void>::I16[r][3]];
		G[skein_constants<void>::I16[r][3]] = rotate_left(G[skein_constants<void>::I16[r][3]],
				skein_constants<void>::C16[r][1]) ^ G[skein_constants<void>::I16[r][2]];
		G[skein_constants<void>::I16[r][4]] += G[skein_constants<void>::I16[r][5]];
		G[skein_constants<void>::I16[r][5]] = rotate_left(G[skein_constants<void>::I16[r][5]],
				skein_constants<void>::C16[r][2]) ^ G[skein_constants<void>::I16[r][4]];
		G[skein_constants<void>::I16[r][6]] += G[skein_constants<void>::I16[r][7]];
		G[skein_constants<void>::I16[r][7]] = rotate_left(G[skein_constants<void>::I16[r][7]],
				skein_constants<void>::C16[r][3]) ^ G[skein_constants<void>::I16[r][6]];
		G[skein_constants<void>::I16[r][8]] += G[skein_constants<void>::I16[r][9]];
		G[skein_constants<void>::I16[r][9]] = rotate_left(G[skein_constants<void>::I16[r][9]],
				skein_constants<void>::C16[r][4]) ^ G[skein_constants<void>::I16[r][8]];
		G[skein_constants<void>::I16[r][10]] += G[skein_constants<void>::I16[r][11]];
		G[skein_constants<void>::I16[r][11]] = rotate_left(G[skein_constants<void>::I16[r][11]],
				skein_constants<void>::C16[r][5]) ^ G[skein_constants<void>::I16[r][10]];
		G[skein_constants<void>::I16[r][12]] += G[skein_constants<void>::I16[r][13]];
		G[skein_constants<void>::I16[r][13]] = rotate_left(G[skein_constants<void>::I16[r][13]],
				skein_constants<void>::C16[r][6]) ^ G[skein_constants<void>::I16[r][12]];
		G[skein_constants<void>::I16[r][14]] += G[skein_constants<void>::I16[r][15]];
		G[skein_constants<void>::I16[r][15]] = rotate_left(G[skein_constants<void>::I16[r][15]],
				skein_constants<void>::C16[r][7]) ^ G[skein_constants<void>::I16[r][14]];
	}

	template<size_t r>
	static inline void KStRv4(uint64_t* G, uint64_t* keys, uint64_t* tweaks)
	{
		G[0] += keys[(r + 0 + 1) % 17];
		G[1] += keys[(r + 1 + 1) % 17];
		G[2] += keys[(r + 2 + 1) % 17];
		G[3] += keys[(r + 3 + 1) % 17];
		G[4] += keys[(r + 4 + 1) % 17];
		G[5] += keys[(r + 5 + 1) % 17];
		G[6] += keys[(r + 6 + 1) % 17];
		G[7] += keys[(r + 7 + 1) % 17];
		G[8] += keys[(r + 8 + 1) % 17];
		G[9] += keys[(r + 9 + 1) % 17];
		G[10] += keys[(r + 10 + 1) % 17];
		G[11] += keys[(r + 11 + 1) % 17];
		G[12] += keys[(r + 12 + 1) % 17];
		G[13] += keys[(r + 13 + 1) % 17] + tweaks[(r + 1) % 3];
		G[14] += keys[(r + 14 + 1) % 17] + tweaks[(r + 2) % 3];
		G[15] += keys[(r + 15 + 1) % 17] + r + 1;
	}

	template<size_t r>
	static inline void G8(uint64_t* G, uint64_t* keys, uint64_t* tweaks)
	{
		GTv4<0>(G);
		GTv4<1>(G);
		GTv4<2>(G);
		GTv4<3>(G);
		KStRv4<r>(G, keys, tweaks);
		GTv4<4>(G);
		GTv4<5>(G);
		GTv4<6>(G);
		GTv4<7>(G);
		KStRv4<r + 1>(G, keys, tweaks);
	}
};

template<size_t N, bool XOF>
class skein_provider
{
public:
	static const bool is_xof = XOF;

	skein_provider(size_t hashsize = N)
		: hs(hashsize)
	{
		validate_hash_size(hashsize, SIZE_MAX);
	}

	~skein_provider()
	{
		clear();
	}

	inline void set_personalization(const std::string& personalization)
	{
		p = personalization;
	}

	inline void set_nonce(const std::string& nonce)
	{
		n = nonce;
	}

	inline void set_key(const std::string& key)
	{
		k = key;
	}

	inline void init()
	{
		squeezing = false;
		tweak[0] = 0ULL;
		pos = 0;
		total = 0;
		zero_memory(H);
		inject_parameter(k, 0ULL);
		tweak[1] = (1ULL << 62) | (4ULL << 56) | (1ULL << 63);
		zero_memory(m);
		m[0] = 0x53;
		m[1] = 0x48;
		m[2] = 0x41;
		m[3] = 0x33;
		m[4] = 0x01;
		uint64_t size64 = XOF ? static_cast<uint64_t>(-1) : hs;
		memcpy(&m[8], &size64, 8);
		transform(m.data(), 1, 32);
		pos = 0;
		total = 0;
		tweak[0] = 0ULL;
		tweak[1] = (1ULL << 62) | (48ULL << 56);
		inject_parameter(p, 8ULL);
		inject_parameter(n, 20ULL);

	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, N / 8, N / 8 + 1, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len, N / 8); });
	}

	inline void squeeze(unsigned char* hash, size_t hs)
	{
		size_t processed = 0;
		if (!squeezing)
		{
			squeezing = true;
			tweak[1] |= 1ull << 63; // last block
			if (pos < N / 8)
				memset(&m[pos], 0, N / 8 - pos);

			transform(m.data(), 1, pos);
			memset(&m[0], 0, N / 8);
			memcpy(&hbk[0], H.data(), N / 8);
			pos = 0;
			total = 0;
		}
		else if (pos < N / 8)
		{
			size_t to_copy = std::min(hs, N / 8 - pos);
			memcpy(hash, reinterpret_cast<unsigned char*>(H.data()) + pos, to_copy);
			processed += to_copy;
			pos += to_copy;
		}
		while (processed < hs)
		{
			pos = std::min(hs - processed, N / 8);
			tweak[0] = 0;
			tweak[1] = 255ULL << 56;
			memcpy(&m[0], &total, 8);
			memcpy(&H[0], hbk.data(), N / 8);
			transform(m.data(), 1, 8);
			memcpy(hash + processed, H.data(), pos);
			processed += pos;
			++total;
		}
	}

	inline void final(unsigned char* hash)
	{
		return squeeze(hash, hs / 8);
	}

	inline size_t hash_size() const
	{
		return hs;
	}

	inline void clear()
	{
		zero_memory(H);
		zero_memory(hbk);
		zero_memory(m);
		zero_memory(tweak);
		zero_memory(p);
		zero_memory(n);
		zero_memory(k);
		p.clear();
		n.clear();
		k.clear();
	}

private:
	inline void transform(const unsigned char* mp, uint64_t num_blks, size_t reallen)
	{
		uint64_t keys[N / 64 + 1];
		uint64_t tweaks[3];

		for (uint64_t b = 0; b < num_blks; b++)
		{
			uint64_t M[N / 64];
			uint64_t G[N / 64];
			for (uint64_t i = 0; i < N / 64; i++)
			{
				M[i] = (reinterpret_cast<const uint64_t*>(mp)[b * N / 64 + i]);
			}
			memcpy(keys, H.data(), sizeof(uint64_t) * N / 64);
			memcpy(tweaks, tweak.data(), sizeof(uint64_t) * 2);
			tweaks[0] += reallen;
			tweaks[2] = tweaks[0] ^ tweaks[1];
			keys[N / 64] = 0x1BD11BDAA9FC1A22ULL;
			for (int i = 0; i < N / 64; i++)
			{
				keys[N / 64] ^= keys[i];
				G[i] = M[i] + keys[i];
			}
			G[N / 64 - 3] += tweaks[0];
			G[N / 64 - 2] += tweaks[1];

			skein_functions<N / 64>::template G8<0>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<2>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<4>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<6>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<8>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<10>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<12>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<14>(G, keys, tweaks);
			skein_functions<N / 64>::template G8<16>(G, keys, tweaks);
			if (N == 1024)
				skein_functions<N / 64>::template G8<18>(G, keys, tweaks);

			tweaks[1] &= ~(64ULL << 56);
			tweak[0] = tweaks[0];
			tweak[1] = tweaks[1];

			for (int i = 0; i < N / 64; i++)
				H[i] = G[i] ^ M[i];
		}
	}

	inline void inject_parameter(const std::string& p, uint64_t code)
	{
		if (p.empty())
			return;

		tweak[1] = (1ULL << 62) | (code << 56);
		update(reinterpret_cast<const unsigned char*>(p.data()), p.length());
		tweak[1] |= 1ull << 63; // last block
		if (pos < N / 8)
			memset(&m[pos], 0, N / 8 - pos);
		transform(m.data(), 1, pos);
		squeezing = false;
		pos = 0;
		total = 0;
		tweak[0] = 0ULL;
		tweak[1] = (1ULL << 62) | (48ULL << 56);
	}

	std::array<uint64_t, N / 64> H, hbk;
	std::array<unsigned char, N / 8> m;
	size_t pos;
	uint64_t total;
	std::array<uint64_t, 2> tweak;
	size_t hs;
	bool squeezing;
	std::string p, n, k;
};


} // namespace detail

} // namespace digestpp

#endif