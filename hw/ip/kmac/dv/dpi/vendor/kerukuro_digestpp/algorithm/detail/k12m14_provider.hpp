/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_K12M14_HPP
#define DIGESTPP_PROVIDERS_K12M14_HPP

#include "../../detail/functions.hpp"
#include "../../detail/absorb_data.hpp"
#include "shake_provider.hpp"
#include <array>

namespace digestpp
{

namespace detail
{

template<size_t B>
class k12m14_provider
{
public:
	static const bool is_xof = true;

	k12m14_provider()
	{
		static_assert(B == 128 || B == 256, "K12M14 only supports 128 and 256 bits");
	}

	~k12m14_provider()
	{
		clear();
	}

	inline void set_customization(const std::string& customization)
	{
		S = customization;
	}

	inline void init()
	{
		main.init();
		pos = 0;
		total = 0;
		chunk = 0;
		squeezing = false;
	}

	inline void update(const unsigned char* data, size_t len)
	{
		detail::absorb_bytes(data, len, m.size(), m.size(), m.data(), pos, total,
			[this](const unsigned char* data, size_t len) { transform(data, len, len * 8192); });
	}

	inline void squeeze(unsigned char* hash, size_t hs)
	{
		if (!squeezing)
		{
			unsigned char buf[B / 4];
			size_t len = shake_functions::right_encode(S.length(), buf, true);
			if (!S.empty())
				update(reinterpret_cast<const unsigned char*>(S.data()), S.length());
			update(buf, len);
			if (pos)
			{
				if (!chunk)
				{
					main.update(m.data(), pos);
					main.set_suffix(0x07);
				}
				else
				{
					child.update(m.data(), pos);
					child.squeeze(buf, B / 4);
					main.update(buf, B / 4);
					main.set_suffix(0x06);
					len = shake_functions::right_encode(chunk, buf, true);
					main.update(buf, len);
					main.update(reinterpret_cast<const unsigned char*>("\xFF\xFF"), 2);
				}
			}
			squeezing = true;
		}
		main.squeeze(hash, hs);
	}

	inline void transform(const unsigned char* data, uint64_t num_blks, size_t reallen)
	{
		(void)reallen;

		for (uint64_t blk = 0; blk < num_blks; blk++)
		{
			if (!chunk)
			{
				main.update(data, 8192);
				main.update(reinterpret_cast<const unsigned char*>("\x03\x00\x00\x00\x00\x00\x00\x00"), 8);
			}
			else
			{
				child.update(data, 8192);
				unsigned char buf[B / 4];
				child.squeeze(buf, B / 4);
				main.update(buf, B / 4);
			}

			child.init();
			child.set_suffix(0x0b);
			++chunk;
			data += 8192;
		}
	}


	inline void clear()
	{
		main.clear();
		child.clear();
		zero_memory(m);
		zero_memory(S);
		S.clear();
	}

private:
	constexpr static size_t R = B == 128 ? 12 : 14;
	shake_provider<B, R> main;
	shake_provider<B, R> child;
	std::array<unsigned char, 8192> m;
	std::string S;
	size_t pos;
	size_t total;
	size_t chunk;
	bool squeezing;
};

} // namespace detail

} // namespace digestpp

#endif // DIGESTPP_PROVIDERS_K12M14_HPP