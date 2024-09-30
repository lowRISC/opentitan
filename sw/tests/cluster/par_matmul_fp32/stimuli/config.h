#ifndef _CONFIG_MATMUL_
#define _CONFIG_MATMUL_

#ifdef FABRIC
#define DATA_LOCATION
#else
#define DATA_LOCATION L1_DATA
#endif

//Define INPUT data types

#ifdef FIXED
    #ifdef FP16
        typedef signed short      v2s    __attribute__((vector_size (4)));
        typedef float16      MA_TYPE;
        typedef float16      MB_TYPE;
        typedef float16      OUT_TYPE;
        typedef float16      MA_VTYPE    __attribute__((vector_size (4)));
        typedef float16      MB_VTYPE    __attribute__((vector_size (4)));
        typedef float16     OUT_VTYPE    __attribute__((vector_size (4)));
        #undef USE_INTRINSICS
    #elif defined(FP16ALT)
        typedef signed short      v2s    __attribute__((vector_size (4)));
        typedef float16alt      MA_TYPE;
        typedef float16alt      MB_TYPE;
        typedef float16alt      OUT_TYPE;
        typedef float16alt      MA_VTYPE    __attribute__((vector_size (4)));
        typedef float16alt      MB_VTYPE    __attribute__((vector_size (4)));
        typedef float16alt     OUT_VTYPE    __attribute__((vector_size (4)));
        #undef USE_INTRINSICS
    #elif defined(FP32)
        typedef float  MA_TYPE;
        typedef float  MB_TYPE;
        typedef float  OUT_TYPE;
    #endif

#else // MIXED
    #ifdef MAFP32
        typedef float      MA_TYPE;
    #elif MAFP16
            typedef signed short      v2s    __attribute__((vector_size (4)));
            typedef float16      MA_TYPE;
            typedef float16      MA_VTYPE    __attribute__((vector_size (4)));
            #undef USE_INTRINSICS
    #elif MAFP16ALT
            typedef signed short      v2s    __attribute__((vector_size (4)));
            typedef float16alt      MA_TYPE;
            typedef float16alt     MA_VTYPE    __attribute__((vector_size (4)));
            #undef USE_INTRINSICS
    #endif
        
    #ifdef MBFP32
            typedef float   MB_TYPE;
    #elif MBFP16
            typedef signed short      v2s    __attribute__((vector_size (4)));
            typedef float16      MB_TYPE;
            typedef float16      MB_VTYPE    __attribute__((vector_size (4)));
            #undef USE_INTRINSICS
    #elif MBFP16ALT
            typedef signed short      v2s    __attribute__((vector_size (4)));
            typedef float16alt      MB_TYPE;
            typedef float16alt     MB_VTYPE    __attribute__((vector_size (4)));
            #undef USE_INTRINSICS
    #endif
        // Define output data types
    #ifdef OUTFP32
            typedef float OUT_TYPE;
    #elif OUTFP16
            typedef signed short      v2s    __attribute__((vector_size (4)));
            typedef float16      OUT_TYPE;
            typedef float16      OUT_VTYPE    __attribute__((vector_size (4)));
    #elif OUTFP16ALT
            typedef signed short      v2s    __attribute__((vector_size (4)));
            typedef float16alt      OUT_TYPE;
            typedef float16alt     OUT_VTYPE    __attribute__((vector_size (4)));
    #endif

#endif

#ifndef THR
    #define THR 0.004f
#endif
#ifdef VECTORIAL
    #if defined(MAFP16) && defined (MBFP16ALT) || defined (MAFP16ALT) && defined (MBFP16) 
        #error "Vecotrization does not work for different data types...!!!" 
    #endif

    #if defined (MAFP32) || defined (MBFP32) || defined (OUTFP32)

        #error "Vecotrization does not work for FP32 data type...!!!" 
    #endif
#endif

void matMul(MA_TYPE * __restrict__ A, MB_TYPE * __restrict__ B, OUT_TYPE * __restrict__ C, int M, int N, int P);

#endif
