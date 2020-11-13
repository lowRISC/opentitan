/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_WHIRLPOOL_HPP
#define DIGESTPP_ALGORITHM_WHIRLPOOL_HPP

#include "../hasher.hpp"
#include "detail/whirlpool_provider.hpp"

namespace digestpp
{

/**
 * @brief Whirlpool hash function
 *
 * @hash
 *
 * @outputsize 512 bits
 *
 * @defaultsize 512 bits
 *
 * @par Example:\n
 * @code // Output a Whirlpool digest of a string
 * digestpp::whirlpool hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code b97de512e91e3828b40d2b0fdce9ceb3c4a71f9bea8d88e75c4fa854df36725fd2b52eb6544edcacd6f8beddfea403cb55ae31f03ad62a5ef54e42ee82c3fb35
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::whirlpool_provider> whirlpool;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_WHIRLPOOL_HPP