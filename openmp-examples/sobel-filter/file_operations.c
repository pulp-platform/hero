/*
 * Copyright 2018 Pedro Melgueira
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "file_operations.h"

#include <stdio.h>
#include <stdlib.h>

#include "macros.h"

/*
 * Reads file to *buffer. Returns file size.
 */

void readFile(char *file_name, byte **buffer, int buffer_size) {
    // Open
    FILE *file = fopen(file_name, "r");

    // Allocate memory for buffer
    *buffer = malloc(sizeof(byte) * buffer_size);

    // Read every char of file ONE BY ONE (not the whole thing at once)
    // We do this because this should look closer to the assembly implementation
    for(int i=0; i<buffer_size; i++) {
        (*buffer)[i] = fgetc(file);
    }

    // Close
    fclose(file);
}

/*
 * Writes the buffer to a file
 */

void writeFile(char *file_name, byte *buffer, int buffer_size) {
    // Open
    FILE *file = fopen(file_name, "w");

    // Write all
    for(int i=0; i<buffer_size; i++) {
        fputc(buffer[i], file);
    }

    // Close
    fclose(file);
}

