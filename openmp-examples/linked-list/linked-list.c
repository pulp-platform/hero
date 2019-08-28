/*
 * HERO Linked List Example Application
 *
 * Copyright 2018 ETH Zurich, University of Bologna
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
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>        // for error codes
#include "bench.h"
#include <hero-target.h>

#ifndef PAYLOAD_SIZE_B
  #define PAYLOAD_SIZE_B 0x100
#endif

typedef struct vertex vertex;

struct vertex {
  unsigned int  vertex_id;
  unsigned int  n_successors;
  vertex**      successors;
  unsigned char payload [PAYLOAD_SIZE_B];
};

int main(int argc, char *argv[])
{
  printf("HERO linked list started.\n");

  char file_name[30] = "tutte.txt";
  if( argc > 1 ) {
    strcpy(file_name, argv[1]);
  }

  /*
   * Read graph from file and generate the linked list
   */
  unsigned int n_vertices = 0;
  unsigned int n_edges = 0;
  unsigned int vertex_from = 0, vertex_to = 0;

  vertex * vertices;

  FILE * fp;
  if ((fp = fopen(file_name, "r")) == NULL) {
    printf("ERROR: Could not open input file.\n");
    return -ENOENT;
  }

  // Parse input file to count the number of vertices.
  // Expected format: vertex_from vertex_to
  while (fscanf(fp, "%u %u", &vertex_from, &vertex_to) != EOF) {
    if (vertex_from > n_vertices)
      n_vertices = vertex_from;
    else if (vertex_to > n_vertices)
      n_vertices = vertex_to;
  }
  n_vertices++;

  // Allocate memory for vertices.
  vertices = (vertex *)malloc(n_vertices*sizeof(vertex));
  if (!vertices) {
    printf("Malloc failed for vertices.\n");
    return -ENOMEM;
  }
  memset((void *)vertices, 0, (size_t)(n_vertices*sizeof(vertex)));

  // Parse input file to count the number of successors of each vertex.
  fseek(fp, 0L, SEEK_SET);
  while (fscanf(fp, "%u %u", &vertex_from, &vertex_to) != EOF) {
    vertices[vertex_from].n_successors++;
    n_edges++;
  }

  // Allocate memory for successor pointers.
  for (unsigned i = 0; i < n_vertices; i++) {
    vertices[i].vertex_id = i;
    if (vertices[i].n_successors > 0) {
      vertices[i].successors = (vertex **)malloc(vertices[i].n_successors*sizeof(vertex *));
      if (!vertices[i].successors) {
        printf("Malloc failed for successors of vertex %d.\n",i);
        return -ENOMEM;
      }
      memset((void *)vertices[i].successors, 0, (size_t)(vertices[i].n_successors*sizeof(vertex *)));
    }
    else
      vertices[i].successors = NULL;
  }

  // Parse input file to set up the successor pointers.
  fseek(fp, 0L, SEEK_SET);
  while (fscanf(fp, "%d %d", &vertex_from, &vertex_to) != EOF) {
    for (unsigned i = 0; i < vertices[vertex_from].n_successors; i++) {
      if (vertices[vertex_from].successors[i] == NULL) {
        vertices[vertex_from].successors[i] = &vertices[vertex_to];
        break;
      }
      else if (i == vertices[vertex_from].n_successors-1) {
        printf("Setting up the successor pointers of virtex %u failed",vertex_from);
        return -1;
      }
    }
  }

  fclose(fp);

  printf("n_vertices = %u\n", n_vertices);
  unsigned int size_b_vertices;
  size_b_vertices = (unsigned int)(n_vertices*sizeof(vertex));

  printf("Total list size = %.3f KiB.\n",
    (float)(size_b_vertices+n_edges*sizeof(vertex *))/1024);

  printf("List start address: %p\n", vertices);

  /*
   * Execute on host
   */
  unsigned n_successors_max = 0;

  bench_start("Host - Max Number of Successors");
  #pragma omp parallel firstprivate(vertices, n_vertices) shared(n_successors_max)
  {
    #pragma omp for reduction(max: n_successors_max)
    for (unsigned i=0; i<n_vertices; i++) {
      if (n_successors_max < vertices[i].n_successors)
        n_successors_max = vertices[i].n_successors;
    }
  }
  bench_stop();
  printf("n_successors_max = %u\n", n_successors_max);

  n_edges = 0;

  bench_start("Host - Number of Edges");
  #pragma omp parallel firstprivate(vertices, n_vertices) shared(n_edges)
  {
    #pragma omp for reduction(+:n_edges)
    for (unsigned i=0; i<n_vertices; i++) {
      n_edges += vertices[i].n_successors;
    }
  }
  bench_stop();
  printf("n_edges = %u\n", n_edges);

  unsigned n_predecessors_max = 0;
  unsigned * n_predecessors = malloc(n_vertices*sizeof(unsigned));
  if (n_predecessors == NULL) {
    printf("ERROR: malloc() failed.\n");
    return -ENOMEM;
  }
  memset((void *)n_predecessors, 0, (size_t)(n_vertices*sizeof(unsigned)));

  bench_start("Host - Max Number of Predecessors");
  #pragma omp parallel firstprivate(vertices, n_vertices) \
    shared(n_predecessors, n_predecessors_max)
  {
    // get the number of predecessors for every vertex
    unsigned n_successors_tmp = 0;
    unsigned vertex_id_tmp    = 0;
    #pragma omp for
    for (unsigned i=0; i<n_vertices; i++) {
      n_successors_tmp = vertices[i].n_successors;
      for (unsigned j=0; j<n_successors_tmp; j++) {
        vertex_id_tmp = vertices[i].successors[j]->vertex_id;
        #pragma omp atomic update
        n_predecessors[vertex_id_tmp] += 1;
      }
    }

    // get the max
    #pragma omp for reduction(max: n_predecessors_max)
    for (unsigned i=0; i < n_vertices; i++) {
      if (n_predecessors[i] > n_predecessors_max)
        n_predecessors_max = n_predecessors[i];
    }
  }
  bench_stop();
  printf("n_predecessors_max = %u\n", n_predecessors_max);

  const unsigned n_successors_max_host   = n_successors_max;
  const unsigned n_edges_host            = n_edges;
  const unsigned n_predecessors_max_host = n_predecessors_max;
  n_successors_max = 0;
  n_edges = 0;
  n_predecessors_max = 0;
  memset((void *)n_predecessors, 0, (size_t)(n_vertices*sizeof(unsigned)));

  /*
   * Excute on PULP
   */

  /*
   * Make sure PULP is ready - speeds up the first target
   */
  unsigned tmp_1 = 1;
  unsigned tmp_2 = 2;
  #pragma omp target device(BIGPULP_SVM) map(to: tmp_1) map(from: tmp_2)
  {
    hero_trywrite(&tmp_2, hero_tryread(&tmp_1));
  }
  tmp_1 = tmp_2;

  bench_start("PULP - Max Number of Successors");
  #pragma omp target device(BIGPULP_SVM) map(to: vertices[0:n_vertices], n_vertices) \
    map(tofrom: n_successors_max)
  {
    unsigned n_vertices_local       = hero_tryread((unsigned int *)&n_vertices);
    unsigned n_successors_max_local = hero_tryread((unsigned int *)&n_successors_max);
    vertex * vertices_local         = (vertex *)hero_tryread((unsigned int *)&vertices);

    #pragma omp parallel firstprivate(vertices_local, n_vertices_local) \
      shared(n_successors_max_local)
    {
      unsigned n_successors_tmp = 0;

      #pragma omp for reduction(max: n_successors_max_local)
      for (unsigned i=0; i<n_vertices_local; i++) {
        n_successors_tmp = hero_tryread((unsigned *)(&(vertices_local[i].n_successors)));

        if (n_successors_max_local < n_successors_tmp)
          n_successors_max_local = n_successors_tmp;
      }
    }

    hero_trywrite(&n_successors_max, n_successors_max_local);
  } // target

  bench_stop();
  printf("n_successors_max = %u\n", n_successors_max);

  bench_start("PULP - Number of Edges");
  #pragma omp target device(BIGPULP_SVM) map(to: vertices[0:n_vertices], n_vertices) \
    map(tofrom: n_edges)
  {
    unsigned n_vertices_local = hero_tryread((unsigned int *)&n_vertices);
    unsigned n_edges_local    = hero_tryread((unsigned int *)&n_edges);
    vertex * vertices_local   = (vertex *)hero_tryread((unsigned int *)&vertices);

    #pragma omp parallel firstprivate(vertices_local, n_vertices_local) \
      shared(n_edges_local)
    {
      #pragma omp for reduction(+:n_edges_local)
      for (unsigned i=0; i<n_vertices_local; i++) {
        n_edges_local += hero_tryread((unsigned *)(&(vertices_local[i].n_successors)));
      }
    }

    hero_trywrite(&n_edges, n_edges_local);
  } // target

  bench_stop();
  printf("n_edges = %u\n", n_edges);

  bench_start("PULP - Max Number of Predecessors");
  #pragma omp target device(BIGPULP_SVM) map(to: vertices[0:n_vertices], n_vertices) \
    map(tofrom: n_predecessors_max, n_predecessors[0:n_vertices])
  {
    unsigned n_vertices_local         = hero_tryread((unsigned int *)&n_vertices);
    unsigned n_predecessors_max_local = hero_tryread((unsigned int *)&n_predecessors_max);
    vertex * vertices_local           = (vertex *)hero_tryread((unsigned int *)&vertices);
    unsigned * n_predecessors_local   = hero_l1malloc(n_vertices_local * sizeof(unsigned));
    if (n_predecessors_local == NULL) {
      printf("ERROR: Memory allocation failed!\n");
    }

    hero_dma_memcpy((void *)n_predecessors_local, (void *)n_predecessors, n_vertices*sizeof(unsigned));

    #pragma omp parallel firstprivate(vertices_local, n_vertices_local, n_predecessors_local) \
      shared(n_predecessors_max_local)
    {
      unsigned n_successors_tmp = 0;
      unsigned vertex_id_tmp    = 0;

      // get the number of predecessors for every vertex
      #pragma omp for
      for (unsigned i=0; i<n_vertices_local; i++) {
        n_successors_tmp = hero_tryread((unsigned *)&vertices_local[i].n_successors);
        for (unsigned j=0; j<n_successors_tmp; j++) {
          hero_tryread((unsigned *)&vertices_local[i].successors[j]);
          vertex_id_tmp = hero_tryread((unsigned *)&(vertices[i].successors[j]->vertex_id));
          #pragma omp atomic update
          n_predecessors_local[vertex_id_tmp] += 1;
        }
      }

      // get the max
      #pragma omp for reduction(max: n_predecessors_max_local)
      for (unsigned i=0; i < n_vertices_local; i++) {
        if (n_predecessors_local[i] > n_predecessors_max_local)
          n_predecessors_max_local = n_predecessors_local[i];
      }
    }

    hero_trywrite(&n_predecessors_max, n_predecessors_max_local);

    hero_dma_memcpy((void *)n_predecessors, (void *)n_predecessors_local, n_vertices*sizeof(unsigned));

    hero_l1free(n_predecessors_local);
  } // target

  bench_stop();
  printf("n_predecessors_max = %u\n", n_predecessors_max);

  // compare results
  if ( (n_successors_max != n_successors_max_host) ||
       (n_edges != n_edges_host) ||
       (n_predecessors_max != n_predecessors_max_host) )
  {
    printf("ERROR: Results do not match between host and PULP.\n");
    return 1;
  }

  // free memory
  free(n_predecessors);
  for (unsigned i = 0; i < n_vertices; i++) {
    free(vertices[i].successors);
  }
  free(vertices);

  return 0;
}
