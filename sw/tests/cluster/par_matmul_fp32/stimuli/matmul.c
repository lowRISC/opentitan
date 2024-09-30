#include "config.h"
#include "pulp.h"

#ifdef VECTORIAL

void __attribute__ ((noinline)) matMul(MA_TYPE * __restrict__ A, MB_TYPE * __restrict__ B, OUT_TYPE * __restrict__ C, int M, int N, int P){

  OUT_VTYPE temp;
  MA_VTYPE Av;
  MB_VTYPE Bv0;
  MB_VTYPE Bv1;
  OUT_VTYPE *Cv;
  int blockSize = (M+NUM_CORES-1)/NUM_CORES;
  int start = get_core_id()*blockSize;
  int end = start + blockSize < M? start + blockSize : M;

  for (int i = start; i < end; i++) {
    for (int j=0; j < (P & 0xfffffffe); j+=2) {
        
      temp = (OUT_VTYPE) {0, 0};

			// Manual unrolling
			for (int k=0; k<(N & 0xfffffffe); k+=2){
				Av  = *((MA_VTYPE *) &A[i*N+k]);
				Bv0 = *((MB_VTYPE *) &B[k*P+j]);
				Bv1 = *((MB_VTYPE *) &B[k*P+j+P]);
				temp += (OUT_VTYPE)(__builtin_shuffle(Av, (v2s){0,0})) * Bv0;
				temp += (OUT_VTYPE)(__builtin_shuffle(Av, (v2s){1,1})) * Bv1;
			}

    if (N & 0x00000001) 
     {
      temp[0] += A[i*N+N-1] * B[(N-1)*P+j];
      temp[1] += A[i*N+N-1] * B[(N-1)*P+j+1];
     }
			Cv = (OUT_VTYPE *) &C[i*P+j];

			*Cv = temp;
    }
  }
  /// Leftover in P
    if (P & 0x00000001) 
    {
      for (int i = start; i < end; i++) {

            OUT_TYPE temp1 = 0;

            // Manual unrolling
            for (int k=0; k<(N & 0xfffffffe); k+=2){
              temp1 += A[i*N+k] * B[k*P+P-1];
              temp1 += A[i*N+k+1] * B[k*P+P-1+P];
            }
          if (N & 0x00000001) 
               {
                temp1 += A[i*N+N-1] * B[(N-1)*P+P-1];
               }
            C[i*P+(P-1)]=temp1;
          }
      }
      
  #if NUM_CORES > 1
  synch_barrier();
  #endif  
}
#else

void __attribute__ ((noinline)) matMul(MA_TYPE * __restrict__ A, MB_TYPE * __restrict__ B, OUT_TYPE * __restrict__ C, int M, int N, int P) {

  int blockSize = (M+NUM_CORES-1)/NUM_CORES;
  int start = get_core_id()*blockSize;
  int end = start + blockSize < M? start + blockSize : M;
  
  for (int i = start; i < end; i++) {
    for (int j = 0; j < P; j++) {
      OUT_TYPE temp = 0;

      //Manual unrolling
      for (int k = 0; k < (N & 0xfffffffe); k+=2) {
        temp += (OUT_TYPE)(A[i*N+k]   * B[k*P+j]);
        temp += (OUT_TYPE)(A[i*N+k+1] * B[k*P+j+P]);

      }
         C[i*P+j] = (OUT_TYPE)(temp);
    }
  }
      // Leftover on N

      if (N & 0x00000001) 
      {
        for (int i=start; i<end; i++) 
        {
          for (int j=0; j<P; j++) 
          {
            C[i*P+j] += (OUT_TYPE)(A[i*N+N-1] * B[(N-1)*P+j]);
          }
        }
      } 

  #if NUM_CORES > 1
  synch_barrier();
  #endif
}
#endif
