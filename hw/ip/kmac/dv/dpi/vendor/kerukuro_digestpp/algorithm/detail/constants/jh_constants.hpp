/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_PROVIDERS_JH_CONSTANTS_HPP
#define DIGESTPP_PROVIDERS_JH_CONSTANTS_HPP

namespace digestpp
{

namespace detail
{

template<typename T>
struct jh_constants
{
	static const uint64_t C[168];

};

template<typename T>
const uint64_t jh_constants<T>::C[168] = {
		0x67f815dfa2ded572ull, 0x571523b70a15847bull, 0xf6875a4d90d6ab81ull, 0x402bd1c3c54f9f4eull,
		0x9cfa455ce03a98eaull, 0x9a99b26699d2c503ull, 0x8a53bbf2b4960266ull, 0x31a2db881a1456b5ull,
		0xdb0e199a5c5aa303ull, 0x1044c1870ab23f40ull, 0x1d959e848019051cull, 0xdccde75eadeb336full,
		0x416bbf029213ba10ull, 0xd027bbf7156578dcull, 0x5078aa3739812c0aull, 0xd3910041d2bf1a3full,
		0x907eccf60d5a2d42ull, 0xce97c0929c9f62ddull, 0xac442bc70ba75c18ull, 0x23fcc663d665dfd1ull,
		0x1ab8e09e036c6e97ull, 0xa8ec6c447e450521ull, 0xfa618e5dbb03f1eeull, 0x97818394b29796fdull,
		0x2f3003db37858e4aull, 0x956a9ffb2d8d672aull, 0x6c69b8f88173fe8aull, 0x14427fc04672c78aull,
		0xc45ec7bd8f15f4c5ull, 0x80bb118fa76f4475ull, 0xbc88e4aeb775de52ull, 0xf4a3a6981e00b882ull,
		0x1563a3a9338ff48eull, 0x89f9b7d524565faaull, 0xfde05a7c20edf1b6ull, 0x362c42065ae9ca36ull,
		0x3d98fe4e433529ceull, 0xa74b9a7374f93a53ull, 0x86814e6f591ff5d0ull, 0x9f5ad8af81ad9d0eull,
		0x6a6234ee670605a7ull, 0x2717b96ebe280b8bull, 0x3f1080c626077447ull, 0x7b487ec66f7ea0e0ull,
		0xc0a4f84aa50a550dull, 0x9ef18e979fe7e391ull, 0xd48d605081727686ull, 0x62b0e5f3415a9e7eull,
		0x7a205440ec1f9ffcull, 0x84c9f4ce001ae4e3ull, 0xd895fa9df594d74full, 0xa554c324117e2e55ull,
		0x286efebd2872df5bull, 0xb2c4a50fe27ff578ull, 0x2ed349eeef7c8905ull, 0x7f5928eb85937e44ull,
		0x4a3124b337695f70ull, 0x65e4d61df128865eull, 0xe720b95104771bc7ull, 0x8a87d423e843fe74ull,
		0xf2947692a3e8297dull, 0xc1d9309b097acbddull, 0xe01bdc5bfb301b1dull, 0xbf829cf24f4924daull,
		0xffbf70b431bae7a4ull, 0x48bcf8de0544320dull, 0x39d3bb5332fcae3bull, 0xa08b29e0c1c39f45ull,
		0x0f09aef7fd05c9e5ull, 0x34f1904212347094ull, 0x95ed44e301b771a2ull, 0x4a982f4f368e3be9ull,
		0x15f66ca0631d4088ull, 0xffaf52874b44c147ull, 0x30c60ae2f14abb7eull, 0xe68c6eccc5b67046ull,
		0x00ca4fbd56a4d5a4ull, 0xae183ec84b849ddaull, 0xadd1643045ce5773ull, 0x67255c1468cea6e8ull,
		0x16e10ecbf28cdaa3ull, 0x9a99949a5806e933ull, 0x7b846fc220b2601full, 0x1885d1a07facced1ull,
		0xd319dd8da15b5932ull, 0x46b4a5aac01c9a50ull, 0xba6b04e467633d9full, 0x7eee560bab19caf6ull,
		0x742128a9ea79b11full, 0xee51363b35f7bde9ull, 0x76d350755aac571dull, 0x01707da3fec2463aull,
		0x42d8a498afc135f7ull, 0x79676b9e20eced78ull, 0xa8db3aea15638341ull, 0x832c83324d3bc3faull,
		0xf347271c1f3b40a7ull, 0x9a762db734f04059ull, 0xfd4f21d26c4e3ee7ull, 0xef5957dc398dfdb8ull,
		0xdaeb492b490c9b8dull, 0x0d70f36849d7a25bull, 0x84558d7ad0ae3b7dull, 0x658ef8e4f0e9a5f5ull,
		0x533b1036f4a2b8a0ull, 0x5aec3e759e07a80cull, 0x4f88e85692946891ull, 0x4cbcbaf8555cb05bull,
		0x7b9487f3993bbbe3ull, 0x5d1c6b72d6f4da75ull, 0x6db334dc28acae64ull, 0x71db28b850a5346cull,
		0x2a518d10f2e261f8ull, 0xfc75dd593364dbe3ull, 0xa23fce43f1bcac1cull, 0xb043e8023cd1bb67ull,
		0x75a12988ca5b0a33ull, 0x5c5316b44d19347full, 0x1e4d790ec3943b92ull, 0x3fafeeb6d7757479ull,
		0x21391abef7d4a8eaull, 0x5127234c097ef45cull, 0xd23c32ba5324a326ull, 0xadd5a66d4a17a344ull,
		0x08c9f2afa63e1db5ull, 0x563c6b91983d5983ull, 0x4d608672a17cf84cull, 0xf6c76e08cc3ee246ull,
		0x5e76bcb1b333982full, 0x2ae6c4efa566d62bull, 0x36d4c1bee8b6f406ull, 0x6321efbc1582ee74ull,
		0x69c953f40d4ec1fdull, 0x26585806c45a7da7ull, 0x16fae0061614c17eull, 0x3f9d63283daf907eull,
		0x0cd29b00e3f2c9d2ull, 0x300cd4b730ceaa5full, 0x9832e0f216512a74ull, 0x9af8cee3d830eb0dull,
		0x9279f1b57b9ec54bull, 0xd36886046ee651ffull, 0x316796e6574d239bull, 0x05750a17f3a6e6ccull,
		0xce6c3213d98176b1ull, 0x62a205f88452173cull, 0x47154778b3cb2bf4ull, 0x486a9323825446ffull,
		0x65655e4e0758df38ull, 0x8e5086fc897cfcf2ull, 0x86ca0bd0442e7031ull, 0x4e477830a20940f0ull,
		0x8338f7d139eea065ull, 0xbd3a2ce437e95ef7ull, 0x6ff8130126b29721ull, 0xe7de9fefd1ed44a3ull,
		0xd992257615dfa08bull, 0xbe42dc12f6f7853cull, 0x7eb027ab7ceca7d8ull, 0xdea83eaada7d8d53ull,
		0xd86902bd93ce25aaull, 0xf908731afd43f65aull, 0xa5194a17daef5fc0ull, 0x6a21fd4c33664d97ull,
		0x701541db3198b435ull, 0x9b54cdedbb0f1eeaull, 0x72409751a163d09aull, 0xe26f4791bf9d75f6ull
};

} // namespace detail

} // namespace digestpp

#endif