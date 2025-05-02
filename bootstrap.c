#include <assert.h>
#include <stddef.h>
#include <stdio.h>

int clyde$main(void *ptr, size_t size);
void clyde$print(char *ptr, size_t size) {
    printf("%.*s\n", (int)size, ptr);
}

int main() {
    clyde$main(NULL, 0);
}



