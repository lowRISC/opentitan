/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_DETAIL_WIDTH_FIXER_HPP
#define DIGESTPP_DETAIL_WIDTH_FIXER_HPP

namespace digestpp
{
namespace detail
{

template<typename T, size_t N>
struct stream_width_fixer
{
	stream_width_fixer(T value) : v(value) {}
	T v;
};

template<typename T, size_t N>
std::ostream& operator<<(std::ostream& ostr, const stream_width_fixer<T, N>& value)
{
	return ostr << std::setw(N) << value.v;
}


} // namespace detail
} // namespace digestpp

#endif // DIGESTPP_DETAIL_WIDTH_FIXER_HPP