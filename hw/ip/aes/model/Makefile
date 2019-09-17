BORING_SSL_PATH=../boringssl

NAME=aes_example
FLAGS=-Wall -O2 -g

ifneq ($(wildcard $(BORING_SSL_PATH)/build/crypto/libcrypto.a),)
	FLAGS+=-DUSE_BORING_SSL
endif

all:
	gcc $(FLAGS) crypto.c aes.c $(NAME).c -o $(NAME) -I$(BORING_SSL_PATH) -L$(BORING_SSL_PATH)/build/crypto -lcrypto -lpthread

clean:
	rm -f $(NAME)
