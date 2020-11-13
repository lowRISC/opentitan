/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_DETAIL_ABSORB_DATA_HPP
#define DIGESTPP_DETAIL_ABSORB_DATA_HPP

namespace digestpp
{

namespace detail
{

// Accumulate data and call the transformation function for full blocks.
template<typename T, typename TF>
inline void absorb_bytes(const unsigned char* data, size_t len, size_t bs, size_t bschk,
		unsigned char* m, size_t& pos, T& total, TF transform)
{
	if (pos && pos + len >= bschk)
	{
		memcpy(m + pos, data, bs - pos);
		transform(m, 1);
		len -= bs - pos;
		data += bs - pos;
		total += bs * 8;
		pos = 0;
	}
	if (len >= bschk)
	{
		size_t blocks = (len + bs - bschk) / bs;
		size_t bytes = blocks * bs;
		transform(data, blocks);
		len -= bytes;
		data += bytes;
		total += (bytes)* 8;
	}
	memcpy(m + pos, data, len);
	pos += len;
}


} // namespace detail

} // namespace digestpp

#endif // DIGESTPP_DETAIL_ABSORB_DATA_HPP