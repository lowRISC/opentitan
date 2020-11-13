/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_BLAKE2_HPP
#define DIGESTPP_PROVIDERS_BLAKE2_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "../../detail/validate_hash_size.hpp"
#include "constants/blake2_constants.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace blake2_functions
{
	static inline void G(int r, int i, uint64_t& a, uint64_t& b, uint64_t& c, uint64_t& d, uint64_t* M)
	{
		a = a + b + M[blake2_constants<void>::S[r][2 * i]];
		d = rotate_right(d ^ a, 32);
		c = c + d;
		b = rotate_right(b ^ c, 24);
		a = a + b + M[blake2_constants<void>::S[r][2 * i + 1]];
		d = rotate_right(d ^ a, 16);
		c = c + d;
		b = rotate_right(b ^ c, 63);
	}

	static inline void G(int r, int i, uint32_t& a, uint32_t& b, uint32_t& c, uint32_t& d, uint32_t* M)
	{
		a = a + b + M[blake2_constants<void>::S[r][2 * i]];
		d = rotate_right(d ^ a, 16);
		c = c + d;
		b = rotate_right(b ^ c, 12);
		a = a + b + M[blake2_constants<void>::S[r][2 * i + 1]];
		d = rotate_right(d ^ a, 8);
		c = c + d;
		b = rotate_right(b ^ c, 7);
	}

	template<typename T>
	static inline void round(int r, T* M, T* v)
	{
		G(r, 0, v[0], v[4], v[8], v[12], M);
		G(r, 1, v[1], v[5], v[9], v[13], M);
		G(r, 2, v[2], v[6], v[10], v[14], M);
		G(r, 3, v[3], v[7], v[11], v[15], M);
		G(r, 4, v[0], v[5], v[10], v[15], M);
		G(r, 5, v[1], v[6], v[11], v[12], M);
		G(r, 6, v[2], v[7], v[8], v[13], M);
		G(r, 7, v[3], v[4], v[9], v[14], M);
	}

	template<typename T>
	inline T IV(int t);

	template<>
	inline uint32_t IV<uint32_t>(int t)
	{
		return blake2s_constants<void>::IV[t];
	}

	template<>
	inline uint64_t IV<uint64_t>(int t)
	{
		return blake2b_constants<void>::IV[t];
	}

	inline void initH(std::array<uint32_t, 8>& H)
	{
		memcpy(&H[0], blake2s_constants<void>::IV, 32);
		H[0] ^= 0x01010000ULL;
	}

	inline void initH(std::array<uint64_t, 8>& H)
	{
		memcpy(&H[0], blake2b_constants<void>::IV, 64);
		H[0] ^= 0x0000000001010000ULL;
	}

	inline void initX(std::array<uint32_t, 8>& H, size_t hs, size_t processed, size_t xoffset, uint32_t rhs)
	{
		memcpy(&H[0], blake2s_constants<void>::IV, 32);
		H[0] ^= std::min(hs - processed, static_cast<size_t>(32));
		H[1] ^= 0x00000020;
		H[2] ^= xoffset;
		H[3] ^= 0x20000000;
		H[3] ^= static_cast<uint16_t>(rhs);
	}

	inline void initX(std::array<uint64_t, 8>& H, size_t hs, size_t processed, size_t xoffset, uint64_t rhs)
	{
		memcpy(&H[0], blake2b_constants<void>::IV, 64);
		H[0] ^= std::min(hs - processed, static_cast<size_t>(64));
		H[0] ^= 0x0000004000000000ULL;
		H[1] ^= xoffset;
		H[1] ^= rhs << 32;
		H[2] ^= 0x0000000000004000ULL;
	}

}

template<typename T, blake2_type type>
class blake2_provider
{
public:
	static const bool is_xof = type == blake2_type::xof;

	blake2_provider(size_t hashsize = N)
		: hs(hashsize), squeezing(false)
	{
		static_assert(sizeof(T) == 8 || sizeof(T) == 4, "Invalid T size");

		if (type == blake2_type::hash)
			detail::validate_hash_size(hashsize, N);
		else if (type == blake2_type::x_hash)
			detail::validate_hash_size(hashsize, N * sizeof(T) * 4 - 16);

		zero_memory(s);
		zero_memory(p);
	}

	~blake2_provider()
	{
		clear();
	}

	inline void init()
	{
		pos = 0;
		total = 0;
		xoffset = 0;
		squeezing = false;

		blake2_functions::initH(H);

		if (type == blake2_type::hash)
			H[0] ^= hash_size()/8;
		else
		{
			H[0] ^= N / 8;
			T rhs = type == blake2_type::x_hash ? static_cast<T>(hs/8) : (static_cast<T>(-1) >> (sizeof(T) * 4));
			if (N == 512)
				H[1] ^= (rhs << (N / 16));
			else
				H[3] ^= rhs;
		}
		H[0] ^= (k.size() << 8);
		H[4] ^= s[0];
		H[5] ^= s[1];
		H[6] ^= p[0];
		H[7] ^= p[1];
		absorb_key();
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, N / 4, N / 4 + 1, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len, false); });
	}

	inline void set_key(const std::string& key)
	{
		if (key.length() > N / 8)
			throw std::runtime_error("invalid key length");

		k = key;
	}

	inline void set_salt(const unsigned char* salt, size_t salt_len)
	{
		if (salt_len && salt_len != N / 32)
			throw std::runtime_error("invalid salt length");

		memcpy(&s[0], salt, salt_len);
	}

	inline void set_personalization(const unsigned char* personalization, size_t personalization_len)
	{
		if (personalization_len && personalization_len != N / 32)
			throw std::runtime_error("invalid personalization length");

		memcpy(&p[0], personalization, personalization_len);
	}

	inline void squeeze(unsigned char* hash, size_t hs)
	{
		size_t processed = 0;
		if (!squeezing)
		{
			if (type == blake2_type::xof)
				total += pos * 8;
			squeezing = true;
			xoffset = 0;
			if (N / 4 != pos)
				memset(&m[pos], 0, N / 4 - pos);
			transform(m.data(), 1, true);
			memcpy(&m[0], H.data(), N / 8);
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
			blake2_functions::initX(H, hs, processed, xoffset++, type == blake2_type::xof ? static_cast<T>(-1) : static_cast<T>(hs));
			H[4] ^= s[0];
			H[5] ^= s[1];
			H[6] ^= p[0];
			H[7] ^= p[1];
			total = N;
			memset(&m[N / 8], 0, m.size() - N / 8);
			transform(m.data(), 1, true);
			pos = std::min(hs - processed, N / 8);
			memcpy(hash + processed, H.data(), pos);
			processed += pos;
		}
	}

	inline void final(unsigned char* hash)
	{
		total += pos * 8;
		if (type == blake2_type::hash)
		{
			if (N / 4 != pos)
				memset(&m[pos], 0, N / 4 - pos);
			transform(m.data(), 1, true);
			memcpy(hash, H.data(), hash_size() / 8);
		}
		else
			squeeze(hash, hs / 8);
	}

	inline void clear()
	{
		zero_memory(H);
		zero_memory(m);
		zero_memory(s);
		zero_memory(p);
		zero_memory(k);
		k.clear();
	}

	inline size_t hash_size() const { return hs; }

private:
	inline void absorb_key()
	{
		if (k.empty())
			return;

		unsigned char key[N / 4];
		memcpy(key, k.data(), k.length());
		if (k.length() != N / 4)
			memset(key + k.length(), 0, N / 4 - k.length());
		update(key, sizeof(key));
	}

	inline void transform(const unsigned char* data, size_t num_blks, bool padding)
	{
		for (size_t blk = 0; blk < num_blks; blk++)
		{
			T M[16];
			for (int i = 0; i < 16; i++)
				M[i] = reinterpret_cast<const T*>(data)[blk * 16 + i];
			uint64_t totalbytes = total / 8 + (padding ? 0 : (blk + 1) * N) / 4;
			T t0 = static_cast<T>(totalbytes);
			T t1 = N == 512 ? 0 : static_cast<T>(totalbytes >> 32);
			T f0 = 0;
			T f1 = 0;
			if (padding)
			{
				f0 = static_cast<T>(-1);
				f1 = 0;
			}

			T v[16];
			memcpy(v, H.data(), sizeof(T) * 8);
			v[8 + 0] = blake2_functions::IV<T>(0);
			v[8 + 1] = blake2_functions::IV<T>(1);
			v[8 + 2] = blake2_functions::IV<T>(2);
			v[8 + 3] = blake2_functions::IV<T>(3);
			v[12] = t0 ^ blake2_functions::IV<T>(4);
			v[13] = t1 ^ blake2_functions::IV<T>(5);
			v[14] = f0 ^ blake2_functions::IV<T>(6);
			v[15] = f1 ^ blake2_functions::IV<T>(7);

			blake2_functions::round(0, M, v);
			blake2_functions::round(1, M, v);
			blake2_functions::round(2, M, v);
			blake2_functions::round(3, M, v);
			blake2_functions::round(4, M, v);
			blake2_functions::round(5, M, v);
			blake2_functions::round(6, M, v);
			blake2_functions::round(7, M, v);
			blake2_functions::round(8, M, v);
			blake2_functions::round(9, M, v);
			if (N == 512)
			{
				blake2_functions::round(10, M, v);
				blake2_functions::round(11, M, v);
			}

			H[0] = H[0] ^ v[0] ^ v[0 + 8];
			H[0 + 4] = H[0 + 4] ^ v[0 + 4] ^ v[0 + 8 + 4];
			H[1] = H[1] ^ v[1] ^ v[1 + 8];
			H[1 + 4] = H[1 + 4] ^ v[1 + 4] ^ v[1 + 8 + 4];
			H[2] = H[2] ^ v[2] ^ v[2 + 8];
			H[2 + 4] = H[2 + 4] ^ v[2 + 4] ^ v[2 + 8 + 4];
			H[3] = H[3] ^ v[3] ^ v[3 + 8];
			H[3 + 4] = H[3 + 4] ^ v[3 + 4] ^ v[3 + 8 + 4];
		}

	}

	constexpr static size_t N = sizeof(T) == 8 ? 512 : 256;
	std::array<T, 8> H;
	std::array<T, 2> s;
	std::array<T, 2> p;
	std::string k;
	std::array<unsigned char, N / 4> m;
	size_t pos;
	uint64_t total;
	size_t hs;
	size_t xoffset;
	bool squeezing;
};

} // namespace detail

} // namespace digestpp

#endif