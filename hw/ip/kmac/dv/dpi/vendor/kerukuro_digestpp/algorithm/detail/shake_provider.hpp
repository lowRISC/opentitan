/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_SHAKE_HPP
#define DIGESTPP_PROVIDERS_SHAKE_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "sha3_provider.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

namespace shake_functions
{
	static inline size_t left_encode(size_t num, unsigned char* buf)
	{
		// first, calculate length
		unsigned char n = 1;
		size_t tmp = num;
		while (tmp >>= 8)
			++n;
		buf[0] = n;
		size_t result = n + 1;
		size_t i = 0;
		while (n)
			buf[n--] = static_cast<unsigned char>(num >> (8*i++));
		return result;
	}

	static inline size_t right_encode(size_t num, unsigned char* buf, bool k12)
	{
		// first, calculate length
		unsigned char n = k12 ? num ? 1 : 0 : 1;
		size_t tmp = num;
		while (tmp >>= 8)
			++n;
		buf[n] = n;
		size_t result = n + 1;
		size_t i = 0;
		while (n--)
			buf[n] = static_cast<unsigned char>(num >> (8*i++));
		return result;
	}

} // namespace shake_functions


template<size_t B, int R>
class shake_provider
{
public:
	static const bool is_xof = true;

	shake_provider()
	{
		static_assert(B == 128 || B == 256, "SHAKE only supports 128 and 256 bits");
	}

	~shake_provider()
	{
		clear();
	}

	inline void set_function_name(const std::string& function_name)
	{
		N = function_name;
	}

	inline void set_customization(const std::string& customization)
	{
		S = customization;
	}

	inline void init()
	{
		zero_memory(A);
		pos = 0;
		total = 0;
		squeezing = false;
		suffix = 0;

		if (!N.empty() || !S.empty())
		{
			unsigned char buf[1024];
			size_t r = rate / 8;
			size_t len = shake_functions::left_encode(r, buf);
			size_t total = len;
			update(buf, len);
			len = shake_functions::left_encode(N.length() * 8, buf);
			total += len;
			update(buf, len);
			if (!N.empty())
				update(reinterpret_cast<const unsigned char*>(N.data()), N.length());
			len = shake_functions::left_encode(S.length() * 8, buf);
			update(buf, len);
			total += len;
			if (!S.empty())
				update(reinterpret_cast<const unsigned char*>(S.data()), S.length());
			total += S.length() + N.length();

			len = r - (total % r);
			memset(buf, 0, len);
			update(buf, len);
		}
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, rate / 8, rate / 8, m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { sha3_functions::transform<R>(data, len, A.data(), rate); });
	}

	inline void set_suffix(unsigned char s)
	{
		suffix = s;
	}

	inline void squeeze(unsigned char* hash, size_t hs)
	{
		size_t r = rate / 8;
		size_t processed = 0;
		if (!squeezing)
		{
			m[pos++] = suffix ? suffix : N.empty() && S.empty() ? 0x1F : 0x04;
			if (r != pos)
				memset(&m[pos], 0, r - pos);
			m[r - 1] |= 0x80;
			sha3_functions::transform<R>(m.data(), 1, A.data(), rate);
			squeezing = true;
		}
		else if (pos < r)
		{
			size_t to_copy = std::min(hs, r - pos);
			memcpy(hash, reinterpret_cast<unsigned char*>(A.data()) + pos, to_copy);
			processed += to_copy;
			pos += to_copy;
		}
		while (processed < hs)
		{
			if (processed)
				sha3_functions::transform<R>(A.data());
			pos = std::min(hs - processed, r);
			memcpy(hash + processed, A.data(), pos);
			processed += pos;
		}
	}

	inline void clear()
	{
		zero_memory(A);
		zero_memory(m);
		zero_memory(N);
		zero_memory(S);
		N.clear();
		S.clear();
	}

private:
	std::array<uint64_t, 25> A;
	std::array<unsigned char, 168> m;
	std::string N;
	std::string S;
	const size_t rate = B == 128 ? 1344 : 1088;
	size_t pos;
	size_t total;
	bool squeezing;
	unsigned char suffix;
};

} // namespace detail

} // namespace digestpp

#endif // DIGESTPP_PROVIDERS_SHAKE_HPP