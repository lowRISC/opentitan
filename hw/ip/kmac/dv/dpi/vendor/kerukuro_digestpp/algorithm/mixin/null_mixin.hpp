/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_MIXINS_NULL_HPP
#define DIGESTPP_MIXINS_NULL_HPP

namespace digestpp
{
namespace mixin
{

/**
 * \brief Empty mixin that does not have any additional fuctions.
 * \sa hasher
 */
template<typename T>
struct null_mixin
{
};

} // namespace mixin
} // namespace digestpp

#endif // DIGESTPP_MIXINS_NULL_HPP