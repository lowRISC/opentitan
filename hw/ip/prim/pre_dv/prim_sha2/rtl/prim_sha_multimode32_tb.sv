// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Multi-mode (32-bit interfaced) SHA-2 hash engine testbench
//
// This testbench is used to perform basic verification of the mutli-mode SHA-2 hash engine and
// to scope an understanding for the requirements for interfacing with the engine, e.g., when
// instantiating it in DMA or HMAC.

// The testbench instantiates the 32-bit multi-mode SHA-2 engine and tests a subset of
// test vectors and the digest output against the expected hash.

module prim_sha_multimode32_tb (
  input logic clk_i,
  input logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
  );

  import prim_sha2_pkg::*;
  // DUT signals
  logic              valid_in;
  sha_fifo32_t       data_in;
  logic              sha_en, hash_start, ready_out;
  digest_mode_e      digest_mode, digest_mode_flag;
  logic              hash_process;
  logic [127:0]      msg_length;
  sha_word64_t [7:0] digest;
  logic              idle;

  // Instantiate DUT: SHA-2 32-bit multi-mode engine
  prim_sha2_32 #(
      .MultimodeEn(1)
  ) u_prim_sha2_multimode32 (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),

    // TODO: Test secret wiping control
    .wipe_secret (1'b0),
    .wipe_v      (32'b0),

    .fifo_rvalid       (valid_in),
    .fifo_rdata        (data_in),
    .fifo_rready       (ready_out),
    .sha_en            (sha_en),
    .hash_start        (hash_start),
    .digest_mode       (digest_mode),
    .hash_process      (hash_process),
    .hash_done         (hash_done_d),
    .message_length    (msg_length),
    .digest,
    .idle
  );

  // TB signals
  typedef enum {
    HASH_INIT,
    HASH_START,
    HASH_INPROGRESS,
    HASH_FINALIZE,
    HASH_WAIT,
    HASH_END
  } sha2_tb_e;
  sha2_tb_e  sha2_tb_state_d, sha2_tb_state_q;

  localparam int MsgCount     = 20 ;   // set this to number of test vectors
  localparam int MaxWordCount = 1022; // set this to max word count in longest message

  localparam int ProcessDelayCycles  = 0;  // set this to # of delay cycles until process = 1
  localparam int WordDelayCycles     = 0; // set this to # of delay cycles between each word input

  typedef struct packed {
    digest_mode_e                   sha_mode;
    int                             msg_length; // # of bits
    sha_word32_t [MaxWordCount-1:0] msg_input;
    sha_word32_t [MaxWordCount-1:0] msg_parsed;
    sha_word64_t [7:0]              expectedHash;
  } test_vector_t;


  test_vector_t [MsgCount-1:0] test_vectors;

  int current_msg_length;
  int msg_counter_q, msg_counter_d;
  int delay_process_counter_q, delay_process_counter_d; // to track stall until process = 1
  int delay_word_counter_q, delay_word_counter_d;       // to track stall until next word is fed
  int word_counter_q, word_counter_d;
  int correct_counter_q, correct_counter_d;

  logic msg_counter_increment, word_counter_increment, word_counter_reset;
  logic hash_done_q, hash_done_d, hash_correct;
  logic disable_delay_word_d, disable_delay_word_q;

  initial begin: message_feeding
    // Selected subset of test vectors from the NIST SHA test vectors
    // https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/Secure-Hashing#shavs

    int i = 0;
    // SHA-2 256 short msg (word-aligned)
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 256;
    test_vectors[i].msg_input         = 256'h09fc1accc230a205e4a208e64a8f204291f581a12756392da4b8c0cf5ef02b95;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'h4f44c1c7fbebb6f9601829f3897bfd650c56fa07844be76489076356ac1886a4;

    #1 i = i + 1;

    // SHA-256 short msg (word-aligned)
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 288;
    test_vectors[i].msg_input         = 288'h4e3d8ac36d61d9e51480831155b253b37969fe7ef49db3b39926f3a00b69a36774366000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hbf9d5e5b5393053f055b380baed7e792ae85ad37c0ada5fd4519542ccc461cf3;

    #1 i = i + 1;

    // SHA-256 short msg (word-aligned)
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 32;
    test_vectors[i].msg_input         = 32'h74ba2521;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hb16aa56be3880d18cd41e68384cf1ec8c17680c45a02b1575dc1518923ae8b0e;

    #1 i = i + 1;

    // SHA-2 512 long msg (word-aligned)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 1024;
    test_vectors[i].msg_input         = 1024'hfd2203e467574e834ab07c9097ae164532f24be1eb5d88f1af7748ceff0d2c67a21f4e4097f9d3bb4e9fbf97186e0db6db0100230a52b453d421f8ab9c9a6043aa3295ea20d2f06a2f37470d8a99075f1b8a8336f6228cf08b5942fc1fb4299c7d2480e8e82bce175540bdfad7752bc95b577f229515394f3ae5cec870a4b2f8;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'ha21b1077d52b27ac545af63b32746c6e3c51cb0cb9f281eb9f3580a6d4996d5c9917d2a6e484627a9d5a06fa1b25327a9d710e027387fc3e07d7c4d14c6086cc;

    #1 i = i + 1;

    // SHA-2 384 short msg (64-bit word-aligned)
    test_vectors[i].sha_mode          = SHA2_384;
    test_vectors[i].msg_length        = 512;
    test_vectors[i].msg_input         = 512'h93035d3a13ae1b06dd033e764aca0124961da79c366c6c756bc4bcc11850a3a8d120854f34290fff7c8d6d83531dbdd1e81cc4ed4246e00bd4113ef451334daa;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 384'h8d46cc84b6c2deb206aa5c861798798751a26ee74b1daf3a557c41aebd65adc027559f7cd92b255b374c83bd55568b45;

    #1 i = i + 1;

    // SHA-2 256 long msg (word-aligned)
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 6848;
    test_vectors[i].msg_input         = 6848'h9c4bdc3b1af6ab9dc7bd2dd90e2e429a07d5dd5c48bb7016fe2ca51d3cbd4f45928ea049e2cd9c6d6f7bcd613773396983a891bbbcaeab28807c32fff5709d2f5d935dabeb1f5b13d53ea190ab155700e701f253c520a834551427ecce03868425e27c2adef4d0d7238d102e131c86a65c6868eb0c1a4f82a47ceaac6e80f48e1104638e6354e3007ef182021691ada40a665b4d38a3885a963de5077feece934a807c9f21487cd810f15fd55d7bb4421882333ff2c43b0353de7fc5a656fcdcf8de2e25c1d783a50115106f8fe282c8ae45588ae28450c602e71fad8dbf65b141a7e0e7ea0ae0b079e5fb9855ce017ef63633f6afebafebcbe02f89dc31f3595062fcae45e87b419fea8918574818ac15dd2a4a020141bad752161f3bb58d1e4b97e9427a793c9f9bab22b63c57af9936c2a65082cfec7a4ec53c3750511b465bcf0f6b30c50c1496b02f3bad04af8e7f6e10ced85c997558bf099bc60f861aa790d6f10fd5d1e6b88216705156fed31868ce8dabb031f11bcae51243f7b4e25865a69bc1b0755e28a8411ad15585b02a384a55a4d49a37c26d38636f108ee695d3e732eb5edec40faa1604d4092c6ddd67eaed6bcfbe8f73316a57f462fc6d8764017f38e8f6609411fff5037bdc51587c181fa7a98340569ce3b677f5e7c1559f5c474d55a379e06463b406b27ba5c4ff3bb1006bd39495380b48a3d23528280c6055d5adcf591a2baa0a84b6f2b14878ba6c201c95d1558d4bd41d00d0eb2834767076f861466bef3bbf25902abd0d70ff18acc4b140c121092490879e527c9e045fd83f4189fb36809b92470a113b6f717d4f6b0e29fe7faefea27089a44dd274eba48a576af18be06673e379f5f9fb7862af1a96d4372ca32bfbc2782bc2592cdc82df8b307573c3e76f6d61b06f9e7c9174d9308892b14f734485522d04ba96fa1948c525b17891e72feca98bc6dfe5d047aec48f3797199d25c101f33a7d180c12cced8fca21b32e5b6839ce26461ce8d0a33b2f4f666b73457f6cc58d2b1cdc1473ebb7ebf68f849ae9f9c1b65c87a1b6bf7bb102a4acbb4dc77bea254b0930c846a7e53a808eb19478d1ab9fa88fc2a10a6d5d77db433ee49f16ac296547d1d64c0961df46187cf21ca9d608b39c153b8df97ad7929ac4b3112551c2023e87e58efa7203d196ae5cde69881a031760294f0852;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hf574ac85532bc0c6c4e7614a2e084dbc49fbc474cda593144af28c5cc5f293f8;

    #1 i = i + 1;

    // SHA-2 256 short msg (word-aligned)
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 512;
    test_vectors[i].msg_input         = 512'h5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a650547208251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'h42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa;

    #1 i = i + 1;

    // SHA-2 512 long msg (64-bit word-aligned)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 13696;
    test_vectors[i].msg_input         = 13696'h1cecb230f8c80f87e65e6a5cf1de4301b2cf1ac7c4ae81c478d875d3c9aaeedb92e6b555fe58760840ba161785d6463e27ea595924505226ce5e424bc48cd19b20d41a95f25fbc2dee5d2dd0613552a26ade4d0a668c9770ac904e457b79d044308088f8bc23087f560f588d6d438eb4e1739fe272aa752b793442c8d6bb136029b0a88745ed8385e1983f58914a23fcf570f7e930f216de9c13c5ddbd99c376732d2249730454c7f7bf8938b59039020e9ffc2889aca2117ff5808b185a080f76bf9d472fb2a5cd014ddf36c15ef64f95c657a6631f404c89a21adacf4709b2992dc187623d9b20650be8589dfc856af0aeb06ba894191822e13cd2caa8efe747413713f2ee60478dbe4da832b20cdb891fad803e5355fcb27b8e7cf1c5e137e5c1a7f3c90d1ccadf31b52e66c8b42bc7e1f9ec0fa41b81a139b7df2de50828dc76b82dcde2f632c52bc9f12285a4e111bb3ab701cf932d58e1600364518c44942813cbe8b41705a67331f94f330585d17619eafe1be78b3d3b30f17f529413759f60d401cda7ceead2944ed318fe9f6eda3d8cedd23c20b911d0b0672e481ce8a24651ff73cd12f8109af9987cb8b850af4fa5b53abd763529e748022dd1e753fb6d49ccefb15b3af5ec0184a95a57dfbdf63e409b8f14174c1ec23a9957fc1f707ec44f897c301748326e81e60d0583ccdb5d753fdd82c8421d25f6b801e4b5ca21cb7088561af7d31348767af949a4a3a50d3c6dcd49b1d38b791ed4f8267bd0fd64173666a0425c38984aae45abaa0bfd537d6c87f039c711c79933644adb4cbb9a2cd9d54a61ac4966e7ca1ab3fdcc8b39208534ffc7e55616511d6cd83c04027297bacaa0ba8bedb834169fea05aef6c60e00fcfec5f6036e2ddc385906c27bf640216e2bb6c1cc9819d9fdd72a79e7022d2506769ac2bfd715b7f155a04cce2d1055e972bd158f0d7e5d5b03d5f405f6663b7befae11335af1f5bf52746aa21feda062fd3850de1f4be8e2f46ce8f9a9a28c82ef69ab06fea9dfc9dae9e69fd5c04801558d3a60d768c3b934591d6a23c75e44003358e1cc26bd387467876e567296f001269bbe3cbe360a4b025b016dbefae9a974df6cca4ed733a95614b7aae9d25489693ba0573388fabfd16a668e70a8987394094e020a74e3ff1f5621da0f445876c0e2ac2eb003b31a2c11408ec4b079e4fb9e307c43dd7000281555edcb34214f92578dcc1eed5de37d193776a159b5861166b93fdf5b0134da18fbeb04e9da9c4763e936638f1fa32b4bf44df1ec74e13f289253c834be229d29badda4aca9e647ce6976693122e19e6d1f1b9bb1dd7bebae62c0e4b0d052da0e3aca92c5b6b3f960b492161b8e253e4760e987f019de7fbed28e1d195f4cf79024bab67c2a8ec7e0739554948af873a35dbe9df14f9261218ac659b592995e7720b5f8182dfc18184d840ae53ee0a547c1a2c5fba81dfb9f317082ce92c0758bd5c440e3e68755ceeb692057d3673cfc329de7584c09b3ff6f927faa8749a694ecee76237eb6e4cbf44b7d307115a08a58b8eb4e62def30bee36389198bd58590c3c82211d112ed711330bb83f7139b9ddfab92613222289536395cdeda2f2a3deb44c25e9219bb9ea28b13966037051666c3928865fa74249227ea5af83de3a0a61bd770d6d943b263257f90e53ab199e14549be41cecfe767adb6006e583e63748bb5eaf7e7f236d59e5415dea53da2afcf0c954e25884827394471952496f0d732f24f8dac53a69a644597e4fd15cb52cf6f8ff38539e161591a21151989c36e9020f0f0bcf48c0205a89970a8b67e5aa4f710ca64512da69bbb9156bd83657b21a681c9904151ad01019d1a4ebc36280e17ca4b496a97576f8d34e2671051bd76176490acb6820bc4f5053a45837d5b69660efebaf2b90443139e40dccd1275fbe83bce88e0b79eefd7846923a8de652556714d2f660d2dc4f34fea54f62265218d59dbab4c4ce6e03d7d1f7f88b3c5e05d73cf2d410e445380ac4786380beb859b51509a55cc7424ab51d59fcfa80e190f98ed1b2026d87d6035f0d71f2979a686b4c5cc89b0b74b95c5143ada159e4dd1533f9f6ff16ab0f69f7ecdf815aff2d3f693b8748430c3713963a734a706ed47352f20acf87b8cd82b39e16f5aff09079942e492d1610ae2114c8b6bb6c875d5a1442543a67b6f798bcaa7f163d747960f7be77102d8a05cff274debdf7376014a1733e085eae75f13a9881abad93d03db77277ba2f81246559c65318b687c5e7200d2e0016a72fd554f1837ea6557d58ffd3b2f3c5fef32b70477e94537e741cb9968eeb34a90c8e323bef55d1c368f9f568908297085968607ec5f9762556fa9698c59163bcf763fd012cf9d6e47a68c1b97a314ca7416650f4;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'h3ed79e61d5843b36b6228023670b333208cf9bf556b1d6fc54e95808dfac2402ae06fb749e45883f21211ff41b28cced38d706390a398afa8f5eee760da041f2;

    #1 i = i + 1;

    // SHA-2 384 long msg (word-aligned)
    test_vectors[i].sha_mode          = SHA2_384;
    test_vectors[i].msg_length        = 32704;
    test_vectors[i].msg_input         = 32704'hc0947efb86d54644087247f9fd95133a94075faf6250a2cc9f20df5393edbe1a4bdee20e90e877781a370a7f00cf9eee7373fc38acc54aba23b0df3f020356c9d95ee18f9352e042a9c4b3949592ccfb8a7a08b262373f02d8ec1abff7c62415d2dd2485765cab2a1de2e941a428c4e83fe32c266ceca82c259e35da5a7f51859e2353f8214efdb8de59548d15d7af3dfc780f9bb22daec0748cdb99137704a2a5f815f07b70017554f19d80d0e8b58328ff5a191b4179472c7fb2020af366f2502412766e09dce8e7716c22bea3fd412a41b4a991723049b43f6220283e9fff056ef391e263b99a00a3687cc54fb0ff6c06c651fc06fc4c769494f8539fd6512da0604abdc4be11054d3a95ce35f5465515371b424604dad946f094745d346e318000a8e87513d760388a75c29ef59c4d38b00f4c7a717a451c1dfb74c1e0e077d77cb34bbee174772cff2587d0d88cbc35d93402ea6ab522e0c4353913022f696c7b73cee6506eb4f141ac0714c59b0ad559924cdd1811d9588c4bad9bc4e16e09a6f15a37874f7e4ef91228b1e453a0e0d931139da218d04d1e44b7a04c80ed74a534d5f7af9e3c0ccf60d4f15e3be41e001a3d703152708621283e6cc29450761f44296fefe458f36a9df21a5bdb3f577754b49fed4621cd3eff2c454fa3fed7bd2a3ce770a839cb73d16a7502bc1a52e5e75e71fd7c4ce81dd268741b375f5f26edf8a75972475c9104244a7c65dbd8f3dc25308a7c57a065a8da404dd7dbd6029543f6d3cbea6e6d3f07e1f15eecb1493af022bbcfacbdbe8a6af30d0cda03fb2b071e06398ac8ae89fd818830b3a58e09a691b9fcb107d27f00d4855cc4afb7b52b6519468f33fdebee7369629a7c6a5131c3ab8bd046468f842ada5201a2de3e9714357a6177026cc000bd7c07fd871b7801ba047041c5c2de3e3773f9a419cb3372815c685c64145c6eac0764f18a6e63920ef0f8c1f521f658c249157d1066e7c926740daaccebaa055d8a18201e53dac0ced7d28e7eb3b4bfa35bbbf46a169b5f4b4ab628e1fa920ff98d8b52e9d1c5d1233f6570098101bd033154d3cfe4377e1967cd9f4c48fdd2a798254f93f00c0e34b2192f3e91c3980a5449e0e9d6a36cb852b8d7b4ddd19790344edec5b898bf2ab75692c4ede499df4b00e45df7c7714f93e198c2c2f8a6dbe86ec927324f2c2cd78462449d4a08ab9ee3a6d64c8bd706b3aeaa1efe5847b13dedd660651a9c63980b6765a7df2d95d659f0fadfd8e4063989d46f99dbc23aba33ce195ae259f6855469d015894fc67ac98871b794e277add9df5d9c685e9de7a878f9178da90e23c5302cef32b865129d37e4dca91781980594920ee665034cb59ea9a604d5d3fcc783223bc1ae9b263cc5fb57fdcc4a8077b8b3f73f1d9372c006d00f30246c97c32c5a031e7a903f0efa5d2f7a48fdf096166b605acf76e033791758f8e0027c1ff17b4e31646be47b9eb36c07d5c06dca755f501fc2d31e74bf268b434fbc34459b2e25e2b3559eeb78a4178bb9bb817b9c3acf7640d3b5eda0a4affbbbc3469bf21a8f19b175f4c651d936f03d18b31154a2e5478f9e2c04e439cd076a3e3a8bbde894bea4f46e74f1f9d41da9fc8bf4653f9b7af85b0b23528eec4fa556997bc63f3cb9d5f9945d20adf6fa4591928d97bbf8f7c333dbb1b44b14bbb333e9d5d3c890f28cadefeaa69da66f58ff4f42b2bb04a6384d2216d0184d33defcb500ad2a9751113706814a70eb642c6e4b7c7deac8709fd26bb96e9ba09f6cda82641c0e59bfabc0618cd5cfcec107050ca4c1ed4b3b3fe93b04587f14e7a6f4da69e71cdf22a37089711061556e32ec1c20466f96f161bb1c5e556ab2f3d4734477d8fb3064416e059ac0cf8a53f54c035ad416af784d6f952f2c0581ab3e7e49f6b554546bcde35d6db0c07559974d47b8338aa0ba4b2e2fe0a6f789f82b3e6f4e47ce54218ff61a54a7dd1d66621672a42a74719da32070d78be8d2c0e5da41e75612376ccfd0c3b66cce8a639cd00c85837c280b9c6ce27da38265edb27b442aaac70536d498e0fac83ac4398ea29bc30449cfeb7f3b0d3ab56a4965db49027d0a96c766e777fa8a83c9d4ce80b5a9c676846d2494b478778b4b8612a76b02493f2784e4509598cd6524c10cba30bdf5a0d40ba02300ab9aebcb25da600accf7122144985719422b36f393da833c60ba4ce2b04674462e0d9e922da74c4de9ed482d0f6a442c800cbddd521f2501187c405664fecfaf8a366c49a660b55de095acf2ee425ef5dbd8c38b07c5e6a670a445d72fb07b63467f1c9898ede16139560519e808ee9ddaf710a5bab30f54ed98230d1a44c189ea4f78260c3619827d971a4906a43c4b06d26cd271d1e73219c1a2a12ca3e949fe0d469c0922a4e833c2b42b4ffe9028e5cf9fba3607b8697b878a3b6eb33bcc0b234fa1989bccbae33e9b66cbfe325c01577006103dc8209b53a282e65dfe3a99f85bdec089d721157397a3828d690ee2d3a85e085b6180028bb31f9e8a7cbb2ef432fb89d20e4452c9708a7d917f660ea90f692449c9b1379985b99e20fb75547f9b9ffb5fb94c21a8edc2c3f3ba8d0f436dd06eef48dac2e3e0f9ec09c49392015f721f1820600b78d8f45c9c63ab6d078a3aee3628232cd38c87922b1f3b70e2461efce58aa997a1f7c75173c1e7ae5f2e50ab04afb5fccf500a98705396778a18489aaf414e4d8b13e4a95f1e6a5cb220baad4327b8ba41f62b04beaacb2e629d9a025c8b78b59ef3f26c4ac05cfe67291ffcd9d653ef904491e0ff6a021ed09dbc3bd6b14f5843619aa21bf0e41de81128a1b005af222403e4341adc65cd3ddf564d03fafabde0238454baf62a409ca07ca3aefbf4db65face06f74819c5122c0f41cdb0a26cdf02578a0e1a57efeb9dc40abd0249a2bbf3f5607ef6498eb54c8f1e1b196eeea6c6bc4a01a493b33dd2a7dec460d6008eb40149972d1bae90077fecd47f87ca9f375a9e7adb0512fa05ce28aa5ec47c46079bca2a37b7af092587b4e2281488301cda8d6209d6968affe0f059443b9f4bb26be91f5a46198a6d4e7d2c5d3eb1c33fe31f9f742dc75688863cb85a62ef057d18b05edff0727aa87d4f9a652dccbf661e5d1a64332cc4686816afe762f6dd324b27cf0edc44419ebb32148a08618c5a324ebb23104d3d662d852635633c3997ab555b2e33164717b12f8212f8f892e3c8fb6bf8ebb22a4b7d92058a8c488276e142e8891c71f3db074dcc46241a38c8886a102aece4f1df0243342f05a2219594f65f65c0dcafb16495db6eb54ee8d319a593023d6afcea61a29c6cf7d27cbc6d7aa90b47dfe363700d95d2d21d0aca24b4ddc803ccb13445b723888a60fdb513d5acc3d802f5b7d4bfe3b9a40e0476509dd5c469937a845489b2cde5d50b47300f52d49bce4e7638b3ae6d52a93f9f466a623d9446bea43620328131b90d3969318288b9ca566843f0dc340576230dae236e7daf6de45a948489ed95926d54684124255a7f75549e7e5657e5fe19872fcee0cae090566f16bea1593aea9260d54a1ff4a5731403f165051d19c887d77175a06d4f387bab63d4600d4748e42557515d3dc330993ee3add0d0ca5cd6c31d1f95ae26ecbbd524d1b050e535cb6a9760c548dc3e6ecb1c5f9eb61f436f14dbd5a9d48a357eb700ba786c3c38aff93d7e3f5c1723f972458359194104b891529ec329a59a2c17a099a0a773d9f898f0b4b3c29c69a4fd061fe83f57271b042b82cbf39fa32dbeab750f4ab3a00e10580909c39497d632063d33718a35ff330d89aa7ba0d8ea74ca57af9c23165a281e8529a52736f6dbeee422f602b5cce8a1bc4609cfc2c900a54667e7ecc242aaea30fcb07ccd6ebe651d9d18e62fe9e98f2288e454e8332ce34a1f71352c2f5c6313682ebce4a5a414ef8c1d5e2bc0fe7ec3585658d291be2d6bbf8427dd8a08323556650e040354a262d74e9432b8f116a89fa50309497f2ab23066ea5cb974ff9eaf9e9bb3f098b87e66f3adcb398900d8431a7c14c5378326585fa5312669715759218a7cd436fe4c2154d47fab8de45b2efdec7b6baedfd020b980e537ae30673e3604e417f71bd3f1b82fd577c6693a46967ac7a5abe7b670baa4ff560de5d64525317521a3b81bbc69e65503fc387c752c4f7fdaf843e231ac3907ea4c38ad553538b65b027c2d6cad2287b8f6f929a209922b715b9a5c49d566865b34d0f358b0422f2bdb1010e7cd0bf4fe7e534ab5736c54d49d942aa27e5403108d56b035dc7669faf81bcc1710c8233e5aeee695b305816a86da5623ee2b06731f71ecd402fdeb311f466ae2c0829cde5373052c11843a9bdd14e8b36f1217ebb1cab01d69fe3d361939f1322360e848318aaf61d41107cf6ceae63c4731bfe00d0803f85ba2e873ae9b69ee838b8ee2bcdaed1c46d6716ef9025aa5bfb185baf9d4ee4d1e11734ea515dbfe262a1616bc0cc645adf8ffe04d074bd61fbaf2e23ed67804fb726631c84e4e4a5566094bf8c743c552a23a8e309fc2b6af738dbea4b5a9053aed4a83ddefcab95767eee839b46b827dfaa8de6972c62fb705deb7f21a893823aca6acad9f573576544d57477b46657628d339c2295f287e986d36f2ac2185fed402140007fea6f855afffeac3dc5684554308016c958a4d52c3a16a1478d51290e6239ecec6f226949a48ea34363ef0a97eb1efe2713b6c5e676123f9960ea806db414e9db8024836999a0e775b03034b0e9e5434fa2423e2e1dfe504841a085e68d6d91cdabea666315d1f34538f02647b35f80a392dba07ba8277dd49df7ac1164a08f2360e874aecf9e61227c8381b4be0a20a343f78f479b1a32bed4746576c05a1c8d4db350a51d728bade98ec9908061cdff540a6d2a6d62f967939b347f26f6c45ba0bf6cfe85db0d480e66505390e2c2f841a8cc8c958e4c8f49c0aba30f03312f28813c13af445071699ec8867629ba3e7b372ff6b9f8a66665a94d7aff1bcd68438d407ce04aefba69bc94a196930e228f5a09e1313e91bd85a96c7f6d8d03a760580ca2cf6b4593bd34472d78bb5954fc65dce4a1cc88c50845bb18d0f37e6d2d66131dd301fc9da29a5292a30f0636210f3b79722f164d9c02abefdfcb981a092bd65681cb7f28d85339698c0abf56bbaa880828d2a4978f64a15cd091eb3e623dd8d5521437d5bcf37e2aba3acf271acc55293c53ce4370e04e0859d2d26ae7009d22da68d114deff934eb42bc037dce91545332efdc1df0a044ae1faf7fff61885c77155b5769cec1b5df03a2d0960856af493c0ad93285666bcff96d69e2dea452bbd576f7b952d78c0f4f2800c4425a8afe4c57857fb39d7d70922c8a5dcfa3dc824ea698456482e3038f143b0f64e70ef8c89c850b638fa11952b78a7b1cce2452e8b2e213ed0cdf44292f2b80564362c11aa284df7e820053a1d51241ae6d4fb60b647f2ed3bbaa598741761e00b6b0e1a8312801eabfc2a5e74dcab96bc888331f82149b00d86cca0f12c4f24a8a1ddedc11197b918e0e988ce859ea3c26f5538cd54c635aaa4c202b69be021d05d3421d09005559360cb3f86e68dc09d1be9dba25cc8fcb7b73e2420f0b585f71fa94d2e285952c01e67e94a79e98bb0f0c99123a3f273a910998bbcd54fcfa14b95d65644f45f135c181c65aa425382907d0fadb4b318e3635ca006941f4d43739243d57076c901bc845f751218b6a67d6c9;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 384'h00d3b9396a09d37e126ecceb86f5db9e8ed94065646f4d3d6bba15e8318ca9f6d07e363d60dd863ec28ac2378ccdb515;

    #1 i = i + 1;

    // SHA-2 256 short msg (not word-aligned)
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 40;
    // msg is padded at the end with zeros and number of bits are adjusted (should be 40)
    test_vectors[i].msg_input         = 64'hc299209682000000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hf0887fe961c9cd3beab957e8222494abb969b1ce4c6557976df8b0f6d20e9166;

    #1 i = i + 1;

    // SHA-2 384 short msg (not word-aligned)
    test_vectors[i].sha_mode          = SHA2_384;
    test_vectors[i].msg_length        = 72;
    // msg is padded at the end with zeros and number of bits are adjusted (should be 72)
    test_vectors[i].msg_input         = 96'h8d45a55d5ce1f928e6000000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'hde76683575a050e2eb5ef95ee201f82416478a1d14bf3d96d1fd4efd52b1a28fed8dfee1830070001dc102a21f761d20;

    #1 i = i + 1;

    // SHA-2 512 short msg (not word-aligned)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 24;
    // msg is padded at the end with zeros and number of bits are adjusted (should be 24)
    test_vectors[i].msg_input         = 32'h0a55db00;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'h7952585e5330cb247d72bae696fc8a6b0f7d0804577e347d99bc1b11e52f384985a428449382306a89261ae143c2f3fb613804ab20b42dc097e5bf4a96ef919b;

    #1 i = i + 1;

    // SHA-2 512 short msg (not word-aligned)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 520;
    // msg is padded at the end with zeros and number of bits are adjusted (should be 520)
    test_vectors[i].msg_input         = 544'hd3ddddf805b1678a02e39200f6440047acbb062e4a2f046a3ca7f1dd6eb03a18be00cd1eb158706a64af5834c68cf7f105b415194605222c99a2cbf72c50cb14bf000000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'hbae7c5d590bf25a493d8f48b8b4638ccb10541c67996e47287b984322009d27d1348f3ef2999f5ee0d38e112cd5a807a57830cdc318a1181e6c4653cdb8cf122;

    #1 i = i + 1;

    // SHA-2 512 short msg (not word-aligned)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 16;
    // msg is padded at the end with zeros and number of bits are adjusted (should be 16)
    test_vectors[i].msg_input         = 32'h90830000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'h55586ebba48768aeb323655ab6f4298fc9f670964fc2e5f2731e34dfa4b0c09e6e1e12e3d7286b3145c61c2047fb1a2a1297f36da64160b31fa4c8c2cddd2fb4;

    #1 i = i + 1;

    // SHA-2 256 short msg (512+32 = 544)
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 544;
    test_vectors[i].msg_input         = 544'h5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a650547208251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509ab801234;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'h44a2d734e1b61bc487c4ece0aaae5996db07481b0b776202da5b77b7f45dd86e;

    #1 i = i + 1;

    // SHA-2 512 word-aligned (1024+32 = 1056)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 1056;
    test_vectors[i].msg_input         = 1056'hfd2203e467574e834ab07c9097ae164532f24be1eb5d88f1af7748ceff0d2c67a21f4e4097f9d3bb4e9fbf97186e0db6db0100230a52b453d421f8ab9c9a6043aa3295ea20d2f06a2f37470d8a99075f1b8a8336f6228cf08b5942fc1fb4299c7d2480e8e82bce175540bdfad7752bc95b577f229515394f3ae5cec870a4b2f8abcd1234;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'h1d6bc5b82e776f49a9f5ff5617249e3ebf6b034da06388d9d07cb6f90aa1e89846127d47d79a6b54921fe4deda651bd0a054e3ac72cdf8ae3dcf0b49a943e1c0;

    #1 i = i + 1;

    // SHA-2 512 long msg word-aligned (1024+64 = 1088)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 1088;
    test_vectors[i].msg_input         = 1088'hfd2203e467574e834ab07c9097ae164532f24be1eb5d88f1af7748ceff0d2c67a21f4e4097f9d3bb4e9fbf97186e0db6db0100230a52b453d421f8ab9c9a6043aa3295ea20d2f06a2f37470d8a99075f1b8a8336f6228cf08b5942fc1fb4299c7d2480e8e82bce175540bdfad7752bc95b577f229515394f3ae5cec870a4b2f8abcd1234abcd1234;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'h9ee5fdf8fd87a75ba752d29639cfbe081bed09816fdc57d2523ff524136394ee8a07f61d9fff187f06c6fc3f3456989aa605dff04c9dc9af887434e10e1a1c7e;

    #1 i = i + 1;

    // SHA-2 512 long msg word-aligned (160)
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 160;
    test_vectors[i].msg_input         = 160'habcd1234feabcd1234feabcd1234fe00001234fe;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'he9b8e43132486237ea5b73cec69f35d35aed9e8babe0df11c0e1da595b787fc7de616868f60571131ceb026dbfd4cef1233639583bae8d1cef736c189a7cb1cd;

    #1 i = i + 1;

    // SHA-2 256 short msg word-aligned
    test_vectors[i].sha_mode          = SHA2_256;
    test_vectors[i].msg_length        = 32;
    test_vectors[i].msg_input         = 32'h00000001;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 256'hb40711a88c7039756fb8a73827eabe2c0fe5a0346ca7e0a104adc0fc764f528d;

    #1 i = i + 1;

    // SHA-2 512 long msg not word-aligned
    test_vectors[i].sha_mode          = SHA2_512;
    test_vectors[i].msg_length        = 5744;
    // msg is padded at the end with zeros and number of bits are adjusted (should be 5744)
    test_vectors[i].msg_input         = 5760'h0038fb422baf0c64b01c968236f4eb56c930b61d863ee45cfb30e819d317f9594283639b53672fbedb50ad33f6a74e8b59d97275ec67298aaa41348eb677eaa6f749302eaa85aa79f77826911ccb5920d3b1c5794d97bbf707f6e02450c8533a0f333d76b10e59095f6c4b09589caa984533aecbdcccb3ffb4a3a3c412e40057db55f6638696ade3cf104e4dcec8472b6cd7b5b3b1d8e48f572ae292572f6c7d395ddb63fb1af07de784b04bc418d7235ad766bb322ba4f53b743237dbbf1516c453ed66067242bd47addfebcae3cf2adaf2be7cb55a05ccac0b74958b74ab40e800861da05242e35c5920cccdd92ae849af2ebf6702566067a27ea3b7aff362f05ab7130444178334605b3bc94e78391ef585ec943e8695d15061aa2f73e4a2b5f3ad1eb4549a6525351ad31aa68142ea261ee85723fc48279ed2b53331ce88622c72a0cb27c2a7d9f147d1dd555b6219ff8521a2b95f7536f2f2a6787d2679ea7c730d3f45472d6685f04ddcc9e2e43c64921004edebca0121f7e5ef608576ab01e026d0d5ce7612a60a8d1cbbf0b8c05b115d0bc39795b0e1d6190df8ff7383c97e164368264587303964b6bc75625b462b00318a820dc96b5b6365a5b47fe0edf391e64c125aef871325919341e2487db66aa95457d52b7dac376a5f54ccd692cef0018f2f13843de1ebee4c0feb8fc9499a0fcabcbb8dab3f78b638108c77bf788d31d3b1fc39e38c3c9e302a96bd013e82807ad8718c20fff17707422b7b98d6685df2f76e5f7727a66df511377b44d829f9416cce982e590ba3679c488e21af4f4a7f3b3a2d31db015a9ffdc1040c966d74805add829d7c7724733099c852db3c4cbf566f9dbe7cdae4520da17c25b2ebc8cc10bb0198c54582cb8973f0b3dd44fe4f87c688a62f6d52f97f37e52fc6e6b6487f779e54a6da66343fe2ae481f6ea80bd013080a9cafc034ce3b682fe80798ba03ee6142ad098225b32daa322850afade1dcbc39dbba25860000;
    test_vectors[i].msg_parsed        = swap_words(test_vectors[i]);
    test_vectors[i].expectedHash[7:0] = 512'ha2d5485c76dfff615f58edfceaf6d256d538e8041a1c5a6507517d08358dcf0ebd27494225b598ab41a69370e11f6f34b8fe1039542ef4439df38b4f5a0449d4;

  end

  function automatic sha_word32_t [MaxWordCount-1:0] swap_words (test_vector_t sha_test_vector);
    automatic bit offset;
    if (sha_test_vector.msg_length % 32 == 0)  offset = 0;
    else                                       offset = 1;

    for (int i = 0; i < sha_test_vector.msg_length/32 + offset; i++) begin
        swap_words[i] = sha_test_vector.msg_input[(sha_test_vector.msg_length/32) - !offset - i];
    end
  endfunction : swap_words

  always_comb begin : hash_engine_tb_fsm
    // DUT
    hash_start                 = 1'b0;
    sha_en                     = 1'b0;
    hash_process               = 1'b0;
    valid_in                   = 1'b0;
    msg_length                 = 128'b0;
    current_msg_length         = (word_counter_q  + 1) * 32; // 32-bit words
    data_in.mask               = 4'hF;
    data_in.data               = 32'h0000_0000;
    digest_mode                = None;

    // TB
    msg_counter_increment      = 1'b0;
    word_counter_increment     = 1'b0;
    word_counter_reset         = 1'b0;
    hash_correct               = 1'b0;
    sha2_tb_state_d            = sha2_tb_state_q;
    delay_process_counter_d    = delay_process_counter_q;
    delay_word_counter_d       = delay_word_counter_q;
    correct_counter_d          = correct_counter_q;
    disable_delay_word_d       = disable_delay_word_q;

    test_done_o   = 1'b0;
    test_passed_o = 1'b0;

    unique case (sha2_tb_state_q)
      HASH_INIT: begin
        word_counter_reset = 1'b1;
        sha_en = 1'b0; // deasserts the engine to reset its state
        // Check that engine is idle before enabling it
        if (idle == 1'b1) sha2_tb_state_d =  HASH_START;
      end
      HASH_START: begin
        sha_en                = 1'b1; // enables the hash engine:
        hash_start            = 1'b1; // only one pulse to start hashing a complete message
        msg_length            = 128'(test_vectors[msg_counter_q].msg_length);
        word_counter_reset    = 1'b1; // reset word counter for new message
        delay_word_counter_d  = 0;   // reset delay word counter
        disable_delay_word_d  = 1'b0;
        digest_mode           = test_vectors[msg_counter_q].sha_mode;
        sha2_tb_state_d       = HASH_INPROGRESS;
        /*// block to test engine reset and recovery: plug this at different points of hashing
        if (msg_counter_q == 9) begin // try different messages
            sha2_tb_state_d =  HASH_START;
            msg_counter_increment = 1'b1;
        end*/
      end
      HASH_INPROGRESS: begin
        sha_en   = 1'b1;
        delay_word_counter_d = delay_word_counter_q + 1;
        msg_length           = 128'(test_vectors[msg_counter_q].msg_length);

        if ((delay_word_counter_q == WordDelayCycles) && !disable_delay_word_q) begin
          valid_in             = 1'b1; // indicates valid message input for the hashing engine
          data_in.data         = test_vectors[msg_counter_q].msg_parsed[word_counter_q];
          delay_word_counter_d = 0; // reset delay counter
          if (ready_out) word_counter_increment = 1'b1; // word has been absorbed so increment

          if (current_msg_length >= test_vectors[msg_counter_q].msg_length) begin
            disable_delay_word_d = 1'b1;
            msg_length           = 128'(test_vectors[msg_counter_q].msg_length);
            // uncomment to assert here or delay by at least 1 cycle (ProcessDelayCycles)
            // in HASH_FINALIZE
            hash_process = 1'b1;
            if (current_msg_length > test_vectors[msg_counter_q].msg_length) begin
              // non-aligned messages
              data_in.mask               = 4'b1000; // byte masking for non-aligned messages
              delay_process_counter_d    = 0;    // reset delay cycles count
              sha2_tb_state_d            = HASH_WAIT;
              //sha2_tb_state_d          = HASH_FINALIZE;
            end else if (current_msg_length == test_vectors[msg_counter_q].msg_length) begin
              if (ready_out) begin // final word consumed
                delay_process_counter_d = 0;    // reset delay cycles count
                sha2_tb_state_d         = HASH_WAIT;
                // sha2_tb_state_d      = HASH_FINALIZE;
                word_counter_reset      = 1'b1;
              end else begin
                  sha2_tb_state_d       = HASH_INPROGRESS;
              end
            end
          end else begin
              sha2_tb_state_d    = HASH_INPROGRESS;
          end
        end else begin
          data_in.data  = test_vectors[msg_counter_q].msg_parsed[word_counter_q];
          if ((current_msg_length >= test_vectors[msg_counter_q].msg_length)
              && disable_delay_word_q) begin
            msg_length = 128'(test_vectors[msg_counter_q].msg_length);
            valid_in   = 1'b1; // indicates valid message input for the hashing engine
            if (current_msg_length > test_vectors[msg_counter_q].msg_parsed[word_counter_q]) begin
              data_in.mask                 = 4'b1000;   // byte masking for non-aligned messages
            end
              if (ready_out) begin
                delay_process_counter_d    = 0; // reset delay cycles count
                delay_word_counter_d       = 0; // reset delay word counter
                hash_process = 1'b1;
                sha2_tb_state_d            = HASH_WAIT;
                word_counter_reset         = 1'b1;
              end
          end else begin
            sha2_tb_state_d = HASH_INPROGRESS;
          end
        end
      end
      HASH_FINALIZE: begin // to test delay cycles until hash_process is fed
        sha_en                     = 1'b1;
        word_counter_reset         = 1'b1;
        delay_process_counter_d  = delay_process_counter_q + 1;
        // feed message length fed at most 1 clock cycle later and keep it fed
        msg_length                 = 128'(test_vectors[msg_counter_q].msg_length);
        if (delay_process_counter_q == ProcessDelayCycles) begin
          hash_process    = 1'b1;
          sha2_tb_state_d = HASH_WAIT;
        end else begin
          sha2_tb_state_d = HASH_FINALIZE;
        end
      end
      HASH_WAIT: begin
        sha_en     = 1'b1;
        msg_length = 128'(test_vectors[msg_counter_q].msg_length);
        if (hash_done_q == 1'b1) begin
          if (digest_mode_flag == SHA2_512) begin
            hash_correct = ({digest [0], digest [1], digest [2], digest [3], digest [4],
                             digest [5], digest [6], digest [7]} == {
                             test_vectors[msg_counter_q].expectedHash[7],
                             test_vectors[msg_counter_q].expectedHash[6],
                             test_vectors[msg_counter_q].expectedHash[5],
                             test_vectors[msg_counter_q].expectedHash[4],
                             test_vectors[msg_counter_q].expectedHash[3],
                             test_vectors[msg_counter_q].expectedHash[2],
                             test_vectors[msg_counter_q].expectedHash[1],
                             test_vectors[msg_counter_q].expectedHash[0]});
          end else if (digest_mode_flag == SHA2_384) begin
            hash_correct = ({digest [0], digest [1], digest [2], digest [3], digest [4],
                             digest [5]} == {
                             test_vectors[msg_counter_q].expectedHash[5],
                             test_vectors[msg_counter_q].expectedHash[4],
                             test_vectors[msg_counter_q].expectedHash[3],
                             test_vectors[msg_counter_q].expectedHash[2],
                             test_vectors[msg_counter_q].expectedHash[1],
                             test_vectors[msg_counter_q].expectedHash[0]});
          end else if (digest_mode_flag == SHA2_256) begin
            hash_correct = ({digest [0][31:0], digest [1][31:0], digest [2][31:0],
                             digest [3][31:0], digest [4][31:0], digest [5][31:0],
                             digest [6][31:0], digest [7][31:0]} == {
                             test_vectors[msg_counter_q].expectedHash[3],
                             test_vectors[msg_counter_q].expectedHash[2],
                             test_vectors[msg_counter_q].expectedHash[1],
                             test_vectors[msg_counter_q].expectedHash[0]});
          end

          correct_counter_d     = hash_correct ? correct_counter_q + 1 : correct_counter_q;
          msg_counter_increment = 1'b1;

          if (msg_counter_q == MsgCount - 1) sha2_tb_state_d =  HASH_END; // done with test vectors
          else                               sha2_tb_state_d =  HASH_START;
        end
        else begin
          sha2_tb_state_d = HASH_WAIT;
        end
      end
      HASH_END: begin
        sha_en          = 1'b0;
        test_done_o     = 1'b1;
        // test passes if hash is correct for all test vectors
        test_passed_o   = correct_counter_q == MsgCount ? 1'b1 : 1'b0;
        sha2_tb_state_d = HASH_END;
      end
      default: begin
        sha2_tb_state_d = HASH_END;
      end
    endcase
  end

  // Keep count of test vectors
  assign msg_counter_d = msg_counter_increment ? msg_counter_q + 'b1 : msg_counter_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : msg_count
    if (!rst_ni) msg_counter_q <= '0;
    else         msg_counter_q <= msg_counter_d;
  end

  // Increment and reset word counter
  assign word_counter_d = word_counter_reset     ? '0                   :
                          word_counter_increment ? word_counter_q + 'b1 :
                          word_counter_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : word_count
    if (!rst_ni) word_counter_q <= '0;
    else if (msg_counter_increment) word_counter_q <= '0; // reset for new message
    else word_counter_q <= word_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : delay_process_count
    if (!rst_ni) delay_process_counter_q <= 0;
    else         delay_process_counter_q <= delay_process_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : delay_word_count
    if (!rst_ni) delay_word_counter_q <= 0;
    else         delay_word_counter_q <= delay_word_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : disable_delay_word
    if (!rst_ni) disable_delay_word_q <= 1'b0;
    else         disable_delay_word_q <= disable_delay_word_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : correct_count
    if (!rst_ni) correct_counter_q <= 0;
    else         correct_counter_q <= correct_counter_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_fsm
    if (!rst_ni) sha2_tb_state_q <= HASH_INIT;
    else         sha2_tb_state_q <= sha2_tb_state_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : digest_ctrl
    if (!rst_ni) hash_done_q <= '0;
    else         hash_done_q <= hash_done_d;
  end

 // Latch SHA-2 configured mode
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                  digest_mode_flag <= None;
    else if (hash_start)          digest_mode_flag <= digest_mode;
    else if (hash_done_q == 1'b1) digest_mode_flag <= None;
    end

endmodule
