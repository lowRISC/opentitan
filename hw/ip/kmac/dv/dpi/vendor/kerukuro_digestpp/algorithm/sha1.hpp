/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_SHA1_HPP
#define DIGESTPP_ALGORITHM_SHA1_HPP

#include "../hasher.hpp"
#include "detail/sha1_provider.hpp"

namespace digestpp
{

/**
 * @brief SHA-1 hash function
 *
 * Note that SHA-1 hash function is considered insecure and is not recommended for new applications.
 *
 * @hash
 *
 * @outputsize 160 bits
 *
 * @defaultsize 160 bits
 *
 * @par Example:\n
 * @code // Output a SHA1 digest of a string
 * digestpp::sha1 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 2fd4e1c67a2d28fced849ee1bb76e7391b93eb12
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::sha1_provider> sha1;

} // namespace digestpp

#endif