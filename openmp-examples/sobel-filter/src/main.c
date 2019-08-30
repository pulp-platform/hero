/*
 * Copyright 2018 Pedro Melgueira
 * Contribution 2018 (C) ETH Zurich and University of Bologna
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

#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <hero-target.h>

#include "macros.h"
#include "sobel.h"
#include "file_operations.h"


#define ARGS_NEEDED 4

int main(int argc, char *argv[]) {
    char *file_in,
         *file_out,
         *file_out_h,
         *file_out_v,
         *file_gray;

    byte *rgb,
         *gray,
         *sobel_h_res,
         *sobel_v_res,
         *contour_img;

    int rgb_size,
        width,
        height;
    int inter_files = 0,
        gray_file = 0;

    // Get arguments
    if(argc < ARGS_NEEDED) {
        printf("sobel file_in file_out 123x456 [-i file_h_out file_v_out] [-g file_gray]\n");
        return 1;
    }

    // File names
    file_in = argv[1];
    file_out = argv[2];

    // Get size of input image
    char *width_token = strtok(argv[3], "x");
    if(width_token) {
        width = atoi(width_token);
    } else {
        printf("Bad image size argument\n");
        return 1;
    }

    char *height_token = strtok(NULL, "x");
    if(height_token) {
        height = atoi(height_token);
    } else {
        printf("Bad image size argument\n");
        return 1;
    }

    rgb_size = width*height*3;

    // Get optional arguments
    int arg_index = ARGS_NEEDED;
    while(arg_index < argc) {
        // If there is a flag to create intermediate files
        if(strcmp(argv[arg_index], "-i") == 0) {
            if(arg_index+3 > argc) {
                printf("sobel file_in file_out 123x456 [-i file_h_out file_v_out] [-g file_gray]\n");
                return 1;
            }

            inter_files = 1;
            file_out_h = argv[arg_index+1];
            file_out_v = argv[arg_index+2];

            arg_index += 3;
        }

        else if(strcmp(argv[arg_index], "-g") == 0) {
            if(arg_index+2 > argc) {
                printf("sobel file_in file_out 123x456 [-i file_h_out file_v_out] [-g file_gray]\n");
                return 1;
            }

            gray_file = 1;
            file_gray = argv[arg_index+1];

            arg_index += 2;
        }

        else {
            printf("Argument \"%s\", is unknown.\n", argv[arg_index]);
            return 1;
        }
    }

    // Read file to rgb and get size
    readFile(file_in, &rgb, rgb_size);

    // Allocation of image buffers
    int gray_size = rgb_size / 3;
    gray = malloc(sizeof(byte) * gray_size);
    sobel_h_res = malloc(sizeof(byte) * gray_size);
    sobel_v_res = malloc(sizeof(byte) * gray_size);
    contour_img = malloc(sizeof(byte) * gray_size);

    omp_set_default_device(BIGPULP_MEMCPY);
    #pragma omp target map(to: rgb[0:rgb_size], width, height) map(from: gray[0:gray_size], sobel_h_res[0:gray_size], sobel_v_res[0:gray_size], contour_img[0:gray_size])
    sobelFilter(rgb, gray, sobel_h_res, sobel_v_res, contour_img, width, height);

    // Write gray image
    if(gray_file) {
        writeFile(file_gray, gray, gray_size);
    }

    // Write image after each sobel operator
    if(inter_files) {
        writeFile(file_out_h, sobel_h_res, gray_size);
        writeFile(file_out_v, sobel_v_res, gray_size);
    }

    // Write sobel img to a file
    writeFile(file_out, contour_img, gray_size);

    free(gray);
    free(sobel_h_res);
    free(sobel_v_res);
    free(contour_img);

    return 0;
}

