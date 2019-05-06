/* rndaddentropy, an RNDADDENTROPY ioctl wrapper
 * Copyright (C) 2012 Ryan Finnie <ryan@finnie.org>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 */

#include <stdio.h>
#include <string.h>
#include <sys/fcntl.h>
#include <sys/ioctl.h>
#include <linux/random.h>

int main(int argc, char *argv[]) {
  struct {
    int entropy_count;
    int buf_size;
    char buf[1024];
  } entropy;

  if(argc > 2) {
    printf("usage: %s [file]\n", argv[0]);
    return 1;
  }
  FILE *inp;
  if(argc == 1) inp = stdin;
  else inp = fopen(argv[1], "r");
  
  if(inp == NULL) {
    printf("fatal error: cannot open file\n");
    return 1;
  }

  int randfd;
  if((randfd = open("/dev/random", O_WRONLY)) < 0) {
    perror("/dev/random");
    return(1);
  }

  int count;
  while((count = fread(entropy.buf, 1, sizeof(entropy.buf), inp)) > 0) {
    entropy.entropy_count = count * 8;
    entropy.buf_size = count;
    if(ioctl(randfd, RNDADDENTROPY, &entropy) < 0) {
      perror("RNDADDENTROPY");
      return(1);
    }
  }

  return(0);
}
