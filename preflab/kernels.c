/********************************************************
 * Kernels to be optimized for the CS:APP Performance Lab
 ********************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "defs.h"

/* 
 * Please fill in the following team struct 
 */
team_t team = {
    "aaa",              /* Team name */

    "Habs",     /* First member full name */
    "abs@nowhdasdaedu",  /* First member email address */

    "",                   /* Second member full name (leave blank if none) */
    ""                    /* Second member email addr (leave blank if none) */
};

/***************
 * ROTATE KERNEL
 ***************/

/******************************************************
 * Your different versions of the rotate kernel go here
 ******************************************************/

/* 
 * naive_rotate - The naive baseline version of rotate 
 */
char naive_rotate_descr[] = "naive_rotate: Naive baseline implementation";
void naive_rotate(int dim, pixel *src, pixel *dst) 
{
    int i, j;

    for (i = 0; i < dim; i++)
	for (j = 0; j < dim; j++)
	    dst[RIDX(dim-1-j, i, dim)] = src[RIDX(i, j, dim)];
}

/* 
 * rotate - Your current working version of rotate
 * IMPORTANT: This is the version you will be graded on


 * rotate: 16-way unroll, write spatial locality(from bottom)
 * didn't use transpose + switch roll
 */
char rotate_descr[] = "rotate: Current working version";
void rotate(int dim, pixel *src, pixel *dst) 
{
    int i,j;
    int offset = (dim<<4);
    int dst_offset = dim*dim-dim;
    dst += dst_offset;//from bottom

    for(i=0; i<dim; i += 16){
        for(j=0; j< dim ; j++ ){
            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;

            *dst++ = *src;
            src += dim;
            //redirect to block head
            src = src - offset + 1;
            dst -= dim + 16;
        }
        //redirect to next chunk
        dst += dim + dst_offset + 16;
        src += offset - dim;
    }
}


/*********************************************************************
 * register_rotate_functions - Register all of your different versions
 *     of the rotate kernel with the driver by calling the
 *     add_rotate_function() for each test function. When you run the
 *     driver program, it will test and report the performance of each
 *     registered test function.  
 *********************************************************************/

void register_rotate_functions() 
{
    add_rotate_function(&naive_rotate, naive_rotate_descr);   
    add_rotate_function(&rotate, rotate_descr);   
    /* ... Register additional test functions here */
}


/***************
 * SMOOTH KERNEL
 **************/

/***************************************************************
 * Various typedefs and helper functions for the smooth function
 * You may modify these any way you like.
 **************************************************************/

/* A struct used to compute averaged pixel value */
typedef struct {
    int red;
    int green;
    int blue;
    int num;
} pixel_sum;

/* Compute min and max of two integers, respectively */
static int min(int a, int b) { return (a < b ? a : b); }
static int max(int a, int b) { return (a > b ? a : b); }

/* 
 * initialize_pixel_sum - Initializes all fields of sum to 0 
 */
static void initialize_pixel_sum(pixel_sum *sum) 
{
    sum->red = sum->green = sum->blue = 0;
    sum->num = 0;
    return;
}

/* 
 * accumulate_sum - Accumulates field values of p in corresponding 
 * fields of sum 
 */
static void accumulate_sum(pixel_sum *sum, pixel p) 
{
    sum->red += (int) p.red;
    sum->green += (int) p.green;
    sum->blue += (int) p.blue;
    sum->num++;
    return;
}

/* 
 * assign_sum_to_pixel - Computes averaged pixel value in current_pixel 
 */
static void assign_sum_to_pixel(pixel *current_pixel, pixel_sum sum) 
{
    current_pixel->red = (unsigned short) (sum.red/sum.num);
    current_pixel->green = (unsigned short) (sum.green/sum.num);
    current_pixel->blue = (unsigned short) (sum.blue/sum.num);
    return;
}

/* 
 * avg - Returns averaged pixel value at (i,j) 
 */
static pixel avg(int dim, int i, int j, pixel *src) 
{
    int ii, jj;
    pixel_sum sum;
    pixel current_pixel;

    initialize_pixel_sum(&sum);
    for(ii = max(i-1, 0); ii <= min(i+1, dim-1); ii++) 
	for(jj = max(j-1, 0); jj <= min(j+1, dim-1); jj++) 
	    accumulate_sum(&sum, src[RIDX(ii, jj, dim)]);

    assign_sum_to_pixel(&current_pixel, sum);
    return current_pixel;
}

/******************************************************
 * Your different versions of the smooth kernel go here
 ******************************************************/

/*
 * naive_smooth - The naive baseline version of smooth 
 */
char naive_smooth_descr[] = "naive_smooth: Naive baseline implementation";
void naive_smooth(int dim, pixel *src, pixel *dst) 
{
    int i, j;

    for (i = 0; i < dim; i++)
	for (j = 0; j < dim; j++)
	    dst[RIDX(i, j, dim)] = avg(dim, i, j, src);
}

/*
 * smooth - Your current working version of smooth. 
 * IMPORTANT: This is the version you will be graded on
 * not loop unrolling yet
 * naive version: 9read + write
 * 1read/write vertical_add + 1read/write horizontal_add + 1 read/write divide
 * care for overflow of short
 * cache index by 1~dim
 */
struct{
    int red;
    int green;
    int blue;
}cache[1024+5][1024+5];


char smooth_descr[] = "smooth: Current working version";
void smooth(int dim, pixel *src, pixel *dst) 
{
    int i,j;
    int index;
    //hortizontal add 
    for( i=0; i < dim ; i++){
        index = i*dim;
        cache[i][0].red = src[index].red + src[index+1].red;
        cache[i][0].green = src[index].green + src[index+1].green;
        cache[i][0].blue = src[index].blue + src[index+1].blue;
        for( j=1; j < dim-1 ; j++){
            index = i*dim+j;
            cache[i][j].red = src[index-1].red + src[index].red + src[index+1].red;
            cache[i][j].green = src[index-1].green + src[index].green + src[index+1].green;
            cache[i][j].blue = src[index-1].blue + src[index].blue + src[index+1].blue;
        }
        index = i*dim+dim-2;
        cache[i][dim-1].red = src[index].red + src[index+1].red;
        cache[i][dim-1].green = src[index].green + src[index+1].green;
        cache[i][dim-1].blue = src[index].blue + src[index+1].blue;
    }
    //vertical add + divide by 9/6
    for( i=1; i < dim-1 ; i++){
        dst[i*dim].red = (cache[i-1][0].red + cache[i][0].red + cache[i+1][0].red)/6;
        dst[i*dim].green = (cache[i-1][0].green + cache[i][0].green + cache[i+1][0].green)/6;
        dst[i*dim].blue = (cache[i-1][0].blue + cache[i][0].blue + cache[i+1][0].blue)/6;
        for( j=1 ; j<dim-1 ;j++){
            index = i*dim+j;
            dst[index].red = (cache[i-1][j].red+cache[i][j].red+cache[i+1][j].red)/9;
            dst[index].green = (cache[i-1][j].green+cache[i][j].green+cache[i+1][j].green)/9;
            dst[index].blue = (cache[i-1][j].blue+cache[i][j].blue+cache[i+1][j].blue)/9;
        }
        dst[i*dim+j].red = (cache[i-1][j].red + cache[i][j].red + cache[i+1][j].red)/6;
        dst[i*dim+j].green = (cache[i-1][j].green + cache[i][j].green + cache[i+1][j].green)/6;
        dst[i*dim+j].blue = (cache[i-1][j].blue + cache[i][j].blue + cache[i+1][j].blue)/6;
    }
    //top+bottom+corner
    dst[0].red = (cache[0][0].red + cache[1][0].red)/4;
    dst[0].green = (cache[0][0].green + cache[1][0].green)/4;
    dst[0].blue = (cache[0][0].blue + cache[1][0].blue)/4;
    for( i=1; i<dim-1; i++){
        dst[i].red = (cache[0][i].red + cache[1][i].red)/6;
        dst[i].green = (cache[0][i].green + cache[1][i].green)/6;
        dst[i].blue = (cache[0][i].blue + cache[1][i].blue)/6;
    }
    dst[dim-1].red = (cache[0][dim-1].red + cache[1][dim-1].red)/4;
    dst[dim-1].green = (cache[0][dim-1].green + cache[1][dim-1].green)/4;
    dst[dim-1].blue = (cache[0][dim-1].blue + cache[1][dim-1].blue)/4;

    int offset = dim*(dim-1);
    dst[offset].red = (cache[dim-2][0].red + cache[dim-1][0].red)/4;
    dst[offset].green = (cache[dim-2][0].green + cache[dim-1][0].green)/4;
    dst[offset].blue = (cache[dim-2][0].blue + cache[dim-1][0].blue)/4;
    for( i=1; i<dim-1; i++){
        dst[offset+i].red = (cache[dim-2][i].red + cache[dim-1][i].red)/6;
        dst[offset+i].green = (cache[dim-2][i].green + cache[dim-1][i].green)/6;
        dst[offset+i].blue = (cache[dim-2][i].blue + cache[dim-1][i].blue)/6;
    }
    dst[offset+dim-1].red = (cache[dim-2][dim-1].red + cache[dim-1][dim-1].red)/4;
    dst[offset+dim-1].green = (cache[dim-2][dim-1].green + cache[dim-1][dim-1].green)/4;
    dst[offset+dim-1].blue = (cache[dim-2][dim-1].blue + cache[dim-1][dim-1].blue)/4; 

}
/********************************************************************* 
 * register_smooth_functions - Register all of your different versions
 *     of the smooth kernel with the driver by calling the
 *     add_smooth_function() for each test function.  When you run the
 *     driver program, it will test and report the performance of each
 *     registered test function.  
 *********************************************************************/

void register_smooth_functions() {
    add_smooth_function(&smooth, smooth_descr);
    add_smooth_function(&naive_smooth, naive_smooth_descr);
    /* ... Register additional test functions here */
}

