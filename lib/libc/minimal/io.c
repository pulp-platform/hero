/*
 * Copyright (C) 2019 ETH Zurich, University of Bologna
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

#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include "hal/pulp.h"
#include <stdint.h>
#include "io.h"
#include <pulp.h>


#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1 && defined(ARCHI_HAS_CLUSTER)
static L1_DATA int io_lock = 0;
#endif



#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1
static int pos_io_uart_enabled = 0;
static PI_L2 uint8_t pos_io_uart_buffer;
#endif



static int errno;
int *__errno() { return &errno; }



int strcmp(const char *s1, const char *s2)
{
    while (*s1 != '\0' && *s1 == *s2)
    {
        s1++;
        s2++;
    }

    return (*(unsigned char *) s1) - (*(unsigned char *) s2);
}



int strncmp(const char *s1, const char *s2, size_t n)
{
    if (n == 0)
        return 0;

    while (n-- != 0 && *s1 == *s2)
    {
        if (n == 0 || *s1 == '\0')
            break;
        s1++;
        s2++;
    }

    return (*(unsigned char *) s1) - (*(unsigned char *) s2);
}



size_t strlen(const char *str)
{
    const char *start = str;

    while (*str)
        str++;
    return str - start;
}



int memcmp(const void *m1, const void *m2, size_t n)
{
    unsigned char *s1 = (unsigned char *) m1;
    unsigned char *s2 = (unsigned char *) m2;

    while (n--)
    {
        if (*s1 != *s2)
        {
            return *s1 - *s2;
        }
        s1++;
        s2++;
    }
    return 0;
}



void *memset(void *m, int c, size_t n)
{
    char *s = (char *)m;
    while (n--)
        *s++ = (char) c;

    return m;
}



void *memcpy(void *dst0, const void *src0, size_t len0)
{
    void *save = dst0;

    char src_aligned = (((size_t) src0) & 3) == 0;
    char dst_aligned = (((size_t) dst0) & 3) == 0;
    char copy_full_words = (len0 & 3) == 0;

    if (src_aligned && dst_aligned && copy_full_words)
    {
        // all accesses are aligned => can copy full words
        uint32_t *dst = (uint32_t *) dst0;
        uint32_t *src = (uint32_t *) src0;

        while (len0)
        {
            *dst++ = *src++;
            len0 -= 4;
        }
    }
    else
    {
        // copy bytewise
        char *dst = (char *) dst0;
        char *src = (char *) src0;

        while (len0)
        {
            *dst++ = *src++;
            len0--;
        }
    }

    return save;
}



void *memmove(void *d, const void *s, size_t n)
{
    char *dest = d;
    const char *src  = s;

    if ((size_t) (dest - src) < n)
    {
        /*
         * The <src> buffer overlaps with the start of the <dest> buffer.
         * Copy backwards to prevent the premature corruption of <src>.
         */

        while (n > 0)
        {
            n--;
            dest[n] = src[n];
        }
    }
    else
    {
        /* It is safe to perform a forward-copy */
        while (n > 0)
        {
            *dest = *src;
            dest++;
            src++;
            n--;
        }
    }

    return d;
}



char *strcpy(char *d, const char *s)
{
	char *dest = d;
	while (*s != '\0')
    {
		*d = *s;
		d++;
		s++;
	}
	*d = '\0';
	return dest;
}



char *strcat(char *dest, const char *src)
{
	strcpy(dest + strlen(dest), src);
	return dest;
}



char *strchr(const char *s, int c)
{
    char tmp = (char) c;

    while ((*s != tmp) && (*s != '\0'))
        s++;

    return (*s == tmp) ? (char *) s : NULL;
}



static void pos_libc_putc_stdout(char c)
{
    *(uint32_t *)(long)(ARCHI_STDOUT_ADDR + STDOUT_PUTC_OFFSET + (hal_core_id()<<3) + (hal_cluster_id()<<7)) = c;
}



#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1
static void pos_libc_putc_uart(char c)
{
    if (pos_io_uart_enabled)
    {
        pos_io_uart_buffer = c;
        uart_write(CONFIG_IO_UART_ITF, &pos_io_uart_buffer, 1);
    }
}
#endif



static void pos_putc(char c)
{
#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1
    pos_libc_putc_uart(c);
#else
    pos_libc_putc_stdout(c);
#endif
}



int puts(const char *s)
{
    char c;
    do
    {
        c = *s;
        if (c == 0)
        {
            pos_putc('\n');
            break;
        }
        pos_putc(c);
        s++;
    } while(1);

    return 0;
}



int fputc(int c, FILE *stream)
{
    pos_putc(c);

    return 0;
}


int pos_libc_fputc_locked(int c, FILE *stream)
{
    pos_putc(c);

    return 0;
}



int putchar(int c)
{
    return fputc(c, stdout);
}


#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1 && defined(ARCHI_HAS_CLUSTER)

static void uart_io_lock()
{
    while (tas_lock_32((int)&io_lock) == -1)
    {
        volatile int i;
        for (i=0; i<100; i++);
    }
}

static void uart_io_unlock()
{
    tas_unlock_32((int)&io_lock, 0);
}

#endif


int pos_libc_prf_locked(int (*func)(), void *dest, char *format, va_list vargs)
{
    int err;

#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1 && defined(ARCHI_HAS_CLUSTER)
    uart_io_lock();
#endif

    err =  pos_libc_prf(func, dest, format, vargs);

#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1 && defined(ARCHI_HAS_CLUSTER)
    uart_io_unlock();
#endif

    return err;
}


static void __attribute__((noreturn)) pos_wait_forever()
{
#if defined(ITC_VERSION)
    if (hal_is_fc())
    {
        hal_itc_enable_clr(0xffffffff);
        while(1) hal_itc_wait_for_interrupt();
    }
    else
    {
#if defined(EU_VERSION) && EU_VERSION >=3
        eu_evt_maskClr(0xffffffff);
        eu_evt_wait();
#endif
    }   
#elif defined(EU_VERSION) && EU_VERSION >=3
    eu_evt_maskClr(0xffffffff);
    eu_evt_wait();
#endif
    while(1);
}


void exit(int status)
{
    apb_soc_status_set(status);

    pos_wait_forever();
}



void abort()
{
    exit(-1);
}



int pos_io_start()
{
#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1

    uart_open(CONFIG_IO_UART_ITF, CONFIG_IO_UART_BAUDRATE);

    pos_io_uart_enabled = 1;

#endif

    return 0;
}



int pos_io_stop()
{
#if defined(CONFIG_IO_UART) && CONFIG_IO_UART == 1

    pos_io_uart_enabled = 0;

    uart_close(CONFIG_IO_UART_ITF);

#endif

  return 0;
}
