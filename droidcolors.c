/*
 * Ashutosh Jain, Hugo Gonzalez and Natalia Stakhanova
 * 
 * droidcolors - Create an image to represent the .dex file
 * 			the image is a ppn file.
 *
 * compile:
 *     gcc -w -g -o droidcolors droidcolors.c -lm
 *
 *
 * Related paper:
 * Enriching Reverse Engineering through Visual Exploration of Android Binaries
 * 5th Program protection and Reverse Engineering Workshop (PPREW-5)
 *  
 * http://dx.doi.org/10.1145/2843859.2843866
 * 
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <getopt.h>
#include <sys/stat.h>

//#include <png.h>  for now we are creating ppn file.
#include <libgen.h>


#define VERSION "0.9"


typedef uint8_t             u1;
typedef uint16_t            u2;
typedef uint32_t            u4;
typedef uint64_t            u8;

/* A coloured pixel. */

typedef struct {
 uint8_t red;
 uint8_t green;
 uint8_t blue;
} pixel_t;

/* A picture. */
    
typedef struct  {
  pixel_t *pixels;
  size_t width;
  size_t height;
} bitmap_t;

typedef struct {
	char dex[3];
	char newline[1];
	char ver[3];
	char zero[1];
} dex_magic;

typedef struct {
	dex_magic magic;
	u4 checksum[1];
	unsigned char signature[20];
	u4 file_size[1];
	u4 header_size[1];
	u4 endian_tag[1];
	u4 link_size[1];
	u4 link_off[1];
	u4 map_off[1];
	u4 string_ids_size[1];
	u4 string_ids_off[1];
	u4 type_ids_size[1];
	u4 type_ids_off[1];
	u4 proto_ids_size[1];
	u4 proto_ids_off[1];
	u4 field_ids_size[1];
	u4 field_ids_off[1];
	u4 method_ids_size[1];
	u4 method_ids_off[1];
	u4 class_defs_size[1];
	u4 class_defs_off[1];
	u4 data_size[1];
	u4 data_off[1];
} dex_header;


typedef struct {
	u4 string_data_off[1];
} string_id_struct;

typedef struct {
	u4 class_idx[1];
	u4 access_flags[1];
	u4 superclass_idx[1];
	u4 interfaces_off[1];
	u4 source_file_idx[1];
	u4 annotations_off[1];
	u4 class_data_off[1];
	u4 static_values_off[1];
} class_def_struct;

typedef struct {
	u2 class_idx[1];
	u2 proto_idx[1];
	u4 name_idx[1];
} method_id_struct;

typedef struct {
	u4 descriptor_idx[1];
} type_id_struct;

typedef struct {
	u4 shorty_idx[1];
    u4 return_type_idx[1];
    u4 parameters_off[1];
} proto_id_struct;

typedef struct {
    u2 class_idx[1];
    u2 type_idx[1];
    u4 name_idx[1];
} field_id_struct;

typedef struct {
    u2 type[1];
    u2 unused[1];
    u4 size[1];
    u4 offset[1];
} map_item_struct;

typedef struct {
	u4 class_annotations_off[1];
	u4 fields_size[1];
	u4 annotated_methods_size[1];
	u4 annotated_parameters_size[1];
	// -- the rest are calculated, they are lists based on the previous sizes
	// field_annotations
	// method_annotations
	// parameter_annotations
	} annotations_directory_item_struct;

typedef struct {
    u2 registers_size[1];
    u2 ins_size[1];
    u2 outs_size[1];
    u2 tries_size[1];
    u4 debug_info_off[1];
    u4 insns_size[1];
    // insns u2[insns_size]  array of bytecode -- dynamic
    // pading u2 -- optional
    // tries try_itme -- optional
    // handlers encoded_catch_handler_list -- optional
} code_item_struct;

typedef struct {
	u4 start_add[1];
	u2 insn_count[1];
	u2 handler_off[1];
} try_item_struct;

const u4 NO_INDEX = 0xffffffff; 

void put_pixel_at (bitmap_t * bitmap, u4 d, u1 r, u1 g, u1 b)
{
	pixel_t *pix = bitmap->pixels + d;
	pix->red = r;
	pix->green = g;
	pix->blue = b;
}

void put_pixels (bitmap_t * bitmap, u4 offset, u4 len, u1 r, u1 g, u1 b)
{
	int x;
	pixel_t * pix = bitmap->pixels + offset;
	for (x=0; x<len; x++) {
		pix->red = r;
		pix->green = g;
		pix->blue = b;
		pix++;
	}
}

static int save_ppm_to_file (bitmap_t *bitmap, const char *path)
{
	FILE * fp;
	fp = fopen (path, "wb");
   if (! fp) {
        fprintf(stderr, "ERROR: Can't create .ppn file!\n");
   }
    
  (void) fprintf(fp, "P6\n%d %d\n255\n", bitmap->width,bitmap->height);
  (void) fwrite(bitmap->pixels, sizeof(pixel_t), bitmap->width*bitmap->height, fp);
 
  fclose (fp);
 
  return 0;
	}

int readUnsignedLeb128(u1** pStream)
{
/* taken from dalvik's libdex/Leb128.h */
    u1* ptr = *pStream;
    int result = *(ptr++);

    if (result > 0x7f) {
        int cur = *(ptr++);
        result = (result & 0x7f) | ((cur & 0x7f) << 7);
        if (cur > 0x7f) {
            cur = *(ptr++);
            result |= (cur & 0x7f) << 14;
            if (cur > 0x7f) {
                cur = *(ptr++);
                result |= (cur & 0x7f) << 21;
                if (cur > 0x7f) {
                    /*
                     * Note: We don't check to see if cur is out of
                     * range here, meaning we tolerate garbage in the
                     * high four-order bits.
                     */
                    cur = *(ptr++);
                    result |= cur << 28;
                }
            }
        }

    }

    *pStream = ptr;
    return result;
}


void ColorStrings(bitmap_t **bitmap, u1 *file, u4 offset, u1 order)
{
    /* Replace the uleb128_value function to put it inline */
    
	u1 size = 0;
    u1 *ptr = file +offset;
    int result = *(ptr++);
    size++;
    if (result > 0x7f) {
        int cur = *(ptr++);
        size++;
        result = (result & 0x7f) | ((cur & 0x7f) << 7);
        if (cur > 0x7f) {
            cur = *(ptr++);
            size++;
            result |= (cur & 0x7f) << 14;
            if (cur > 0x7f) {
                cur = *(ptr++);
                size++;
                result |= (cur & 0x7f) << 21;
                if (cur > 0x7f) {
                    cur = *(ptr++);
                    size++;
                    result |= cur << 28;
                }
            }
        }
    } 
    
    put_pixels ( bitmap,offset, size , 240,0,0);  // string_ids  -- red
    put_pixels ( bitmap,offset + size, result , order*100,109,44);  // string_ids  -- darkgreen
    
}


int Analize_class_data(bitmap_t **bitmap, u1 *file, u4 offset)
{
	u4 static_fields_size;
	u4 instance_fields_size;
	u4 direct_methods_size;
	u4 virtual_methods_size;
	u4 discard;
	u4 i,j;
	u4 code_off;
	code_item_struct* code_item;
	int padding = 0;

	u1 *ptr = file + offset;
	
	static_fields_size = readUnsignedLeb128( &ptr);
	instance_fields_size = readUnsignedLeb128( &ptr);
	direct_methods_size = readUnsignedLeb128( &ptr);
	virtual_methods_size = readUnsignedLeb128( &ptr);

	for (i=0; i<static_fields_size; i++)
	{
		discard = readUnsignedLeb128( &ptr);  	// field_idx_diff
		discard = readUnsignedLeb128( &ptr);	// access_flags
	}
    
    for (i=0; i<instance_fields_size; i++)
	{
		discard = readUnsignedLeb128( &ptr);  	// field_idx_diff
		discard = readUnsignedLeb128( &ptr);	// access_flags
	}
	
	for (i=0; i<direct_methods_size; i++)
	{
		discard = readUnsignedLeb128( &ptr);  	// method_idx_diff
		discard = readUnsignedLeb128( &ptr);	// access_flags
		code_off = readUnsignedLeb128( &ptr);	// code_off  if 0 means abstract or native. Follow the code item.
		if (code_off !=0 ) {
				code_item = (code_item_struct *) (file + code_off);
				put_pixels( bitmap,code_off, sizeof(code_item), 84,39,136);  // head of Direct Methods   -- purple
				put_pixels( bitmap,code_off+sizeof(code_item), *code_item->insns_size * sizeof(u2) , 153,142,195);  // Code Direct Methods  lightpurple
				if (*code_item->tries_size > 0) {  //There are tries, more space
					if (*code_item->insns_size % 2 == 1)  padding = 2;
					  put_pixels( bitmap,code_off+sizeof(code_item)+*code_item->insns_size * sizeof(u2)+padding, *code_item->tries_size * sizeof(try_item_struct) , 153,142,0);  // Try on Direct Methods  lightpurple
					}
				//TODO deal with the handlers and encoded_catch_handler_list, which is a dynamic structure.	

				if (*code_item->debug_info_off !=0) {
					u1 *ptr2 = file + *code_item->debug_info_off;
					discard = readUnsignedLeb128( &ptr2); // line_start
					u4 parameter_size = readUnsignedLeb128( &ptr2); // parameter_size
					for (j=0; j<parameter_size; j++) discard = readUnsignedLeb128( &ptr2);  // parameter_names array uleb128p1[parameters_size]
					put_pixels(bitmap, *code_item->debug_info_off, ptr2 - (file + *code_item->debug_info_off) , 255,10,235);  // debug info 
				}

		}
	}
	
	for (i=0; i<virtual_methods_size; i++)
	{
		discard = readUnsignedLeb128( &ptr);  	// method_idx_diff
		discard = readUnsignedLeb128( &ptr);	// access_flags
		code_off = readUnsignedLeb128( &ptr);	// code_off  if 0 means abstract or native. Follow the code item.
		if (code_off !=0 ) {
				code_item = (code_item_struct *) (file + code_off);
				put_pixels( bitmap,code_off, sizeof(code_item), 179,88,6);  // head of Direct Methods   -- purple
				put_pixels( bitmap,code_off+sizeof(code_item), *code_item->insns_size * sizeof(u2) , 241,163,64);  // Code Direct Methods  lightpurple
				if (*code_item->tries_size > 0) {  //There are tries, more space
					if (*code_item->insns_size % 2 == 1)  padding = 2;
					  put_pixels( bitmap,code_off+sizeof(code_item)+*code_item->insns_size * sizeof(u2)+padding, *code_item->tries_size * sizeof(try_item_struct) , 153,142,0);  // Try on Direct Methods  lightpurple
					}
				//TODO deal with the handlers and encoded_catch_handler_list, which is a dynamic structure.	
				if (*code_item->debug_info_off !=0) {
					u1 *ptr2 = file + *code_item->debug_info_off;
					discard = readUnsignedLeb128( &ptr2); // line_start
					u4 parameter_size = readUnsignedLeb128( &ptr2); // parameter_size
					for (j=0; j<parameter_size; j++) discard = readUnsignedLeb128( &ptr2);  // parameter_names array uleb128p1[parameters_size]
					put_pixels(bitmap, *code_item->debug_info_off, ptr2 - (file + *code_item->debug_info_off) , 235,0,255);  // debug info 
				}

		}
	}
    
     
    u4 diff = ptr - (file + offset);
    put_pixels (bitmap, offset , diff , 0,150,0);  // Encoded values
	
	}

int Analyze_encoded_value(bitmap_t **bitmap, u1 *file, u4 offset)
{
	//encoded_array format  size=uleb128 + encoded_values[size]
	//Analyze_encoded_value(&dexpng, fileinmemory, *class_def_list->static_values_off); // This is a dynamic structure
	//printf("Analyzing encoded values\n");
	int i;
	u1 VaVt = 0;
    u1 *ptr = file +offset;
    
    int result = readUnsignedLeb128( &ptr);
    for (i=0; i<result; i++)
    {
		VaVt = *(ptr++);  // (Value_arg << 5) | value_type
		ptr+=(VaVt & 00000111)+1;  // extracting the size of the encoded value and move the pointer, do not care about value.
	}
    
    u4 diff = ptr - (file + offset);
    put_pixels (bitmap, offset , diff , 155,150,0);  // Encoded values
	}


void help_show_message(char name[])
{
	printf ("\n=== Droidcolors %s - (c) 2015 \n", VERSION);
    printf( "Paper: Enriching Reverse Engineering through Visual Exploration of Android Binaries\n");
    printf ("5th Program protection and Reverse Engineering Workshop (PPREW-5)\n");
    printf ("http://dx.doi.org/10.1145/2843859.2843866\n===\n");
    printf ("Usage: %s  <file.dex> [sl]\n",name);
    printf( "\t-s\tsilence, no headers\n");
    printf( "\t-l\tlog, create log file from the image\n");
 
}


int main(int argc, char *argv[])
{
	char *dexfile;
	char *outputname;
	char *outputnamedat;
	
	FILE *output;
	FILE *input;
    u1 *fileinmemory;
	int i;
    int SILENCE=0;
    int LOG=0;
    char c;

	bitmap_t dexpng;
   	u4 x;
   	int y;

	u4 static_fields_size;
	u4 instance_fields_size;
	u4 direct_methods_size;
	u4 virtual_methods_size; 

	int field_idx_diff;
	int field_access_flags;

	int method_idx_diff;
	int method_access_flags;
	int method_code_off;

    int are_sorted=1;

	dex_header* header;

	string_id_struct* string_id_list;
	
	method_id_struct* method_id_list;
	type_id_struct* type_id_list;
	proto_id_struct* proto_id_list;
    field_id_struct* field_id_list;
	class_def_struct* class_def_list;
	map_item_struct* map_item;
	
	annotations_directory_item_struct* annotations_directory_list;
	

	if (argc < 2) {
		help_show_message(argv[0]);
		return 1;
	}

	dexfile=argv[1];
	
	outputname = malloc(255*sizeof(u1));
	
	char *path = strdup(dexfile);	
	char *path2 = basename(path);
	//printf("%s\n",path2);
	strcat(outputname,path2);
	strcat(outputname,".ppn\0");
	//printf("%s\n",outputname);
	
	
	
	input = fopen(dexfile, "rb");
	if (input == NULL) {
		fprintf(stderr, "ERROR: Can't open dex file!\n");
		perror(dexfile);
		exit(1);
	}

	//printf("value of c is :%c",getopt(argc, argv, "sl")));
    
    while ((c = getopt(argc, argv, "sl")) != -1) {
                switch(c) {
            case 's':
                SILENCE =1 ;
                break;
            case 'l':
            	LOG=1;
            	break;

            default:
                     help_show_message(argv[0]);
                     return 1;
                }
    }
   
 if (SILENCE>0)
    {  
    printf( "\n=== %s %s - (c) 2015 \n", argv[0],VERSION);
    printf( "Paper: Enriching Reverse Engineering through Visual Exploration of Android Binaries\n");
    printf( "5th Program protection and Reverse Engineering Workshop (PPREW-5)\n");
    printf( "http://dx.doi.org/10.1145/2843859.2843866\n===\n");
    printf( "Usage: %s  <file.dex> [sl]\n",argv[0]);
    printf( "\t-s\tsilence, no headers\n");
    printf( "\t-l\tlog, create log file from the image\n");
   }
   
	
    
    // Obtain the size of the file
    int fd = fileno(input);
    struct stat buffs;
    fstat(fd,&buffs);
    int filesize = buffs.st_size;

    // allocate memory, load all the file in memory
    fileinmemory = malloc(filesize*sizeof(u1));
    if (fileinmemory == NULL) {
        fprintf(stderr, "ERROR: Can't allocate memory for .dex file!\n");
    }
	fread(fileinmemory,1,filesize,input); // file in memory contains the binary
    fclose(input);

	header = (struct dex_header *)fileinmemory;
	
	if (filesize != *header->file_size) {
		printf("Size of the file and reported filesize are different, it will cause errors!\n");
		free(fileinmemory);
		exit(-1);
		}

	dexpng.width = 256;
   	//dexpng.height = round(filesize/256)+1;
	//printf ("PPN file %d x and %d y\n", dexpng.width, dexpng.height);

	dexpng.height = round(*header->file_size/256)+1;
	printf ("PPN file %d x and %d y\n", dexpng.width, dexpng.height);

   	dexpng.pixels = calloc(sizeof (pixel_t), dexpng.width * dexpng.height);
	//dexpng.pixels = malloc(filesize*sizeof (pixel_t));
	
	if (dexpng.pixels == NULL) {
        fprintf(stderr, "ERROR: Can't allocate memory for .png file!\n");
    }

    /* Creating Log */
    if(LOG){


	    printf("%-25s%6s\n","Dex file:",dexfile);   
	    printf("%-25s%6d\n","File size",*header->file_size);
	    printf("%-25s%6d\n","Header Size(bytes)",*header->header_size);
	    printf("%-33s0x%x\n","Header Size",*header->header_size);

	    printf("\n\n");
	    printf("%-25s%6d\n","Link_size",*header->link_size);
	    printf("%-35s%6x hex\n","Link_offset", *header->link_off);
	    printf("%-35s%6x hex\n","Map_offset", *header->map_off);
	    printf("%-25s%6d\n","String_size", *header->string_ids_size);
	    printf("%-35s%6x hex\n","String_Offset", *header->string_ids_off);
	    printf("%-25s%6d\n","Type_size", *header->type_ids_size);
	    printf("%-35s%6x hex\n","Type_offset", *header->type_ids_off);
	    printf("%-25s%6d\n","Prototype_size", *header->proto_ids_size);
	    printf("%-35s%6x hex\n","Prototype_offset", *header->proto_ids_off);
	    printf("%-25s%6d\n","Field_size", *header->field_ids_size);
	    printf("%-35s%6x hex\n","Field_offset", *header->field_ids_off);
	    printf("%-25s%6d\n","Method_size", *header->method_ids_size);
	    printf("%-35s%6x hex\n","Method_offset", *header->method_ids_off);
	    printf("%-25s%6d\n","Class_size", *header->class_defs_size);
	    printf("%-35s%6x hex\n","Class_offset", *header->class_defs_off);
	    printf("%-25s%6d\n","Data_size", *header->data_size);
	    printf("%-35s%6x hex\n","Data_offset", *header->data_off);
	    printf("\n\n");

	  	printf("%-30s%6d\n","Width",dexpng.width);
	  	printf("%-30s%6d\n","Height",dexpng.height);

	  	
		

	}


	/* print dex header information */   
	 if ((strncmp(header->magic.dex,"dex",3) != 0) || 
	     (strncmp(header->magic.newline,"\n",1) != 0) || 
	     (strncmp(header->magic.zero,"\0",1) != 0 ) ) {
		fprintf (stderr, "ERROR: not a dex file\n");
		fclose(input);
		exit(1);
	    }

	//put_pixels( &dexpng, *header->data_off, *header->data_size*sizeof(u1), 100,100,100); // data grey


	if (strncmp(header->magic.ver,"035",3) != 0) {
		fprintf (stderr,"Warning: Dex file version != 035\n");
	}

	if (*header->header_size != 0x70) {
		fprintf (stderr,"Warning: Header size != 0x70\n");
	}
	put_pixels (&dexpng, 0 ,*header->header_size, 255,0,0);  // header -- red

	if (*header->endian_tag != 0x12345678) {
		fprintf (stderr,"Warning: Endian tag != 0x12345678\n");
	}

	/* check the link stuff */
	if (*header->link_size != 0 && *header->link_off !=0 ){
		put_pixels (&dexpng, *header->data_off + *header->data_size+*header->link_off ,*header->link_size, 255,255,0);  // link -- orange
	}
	
	/* check the map stuff the offset should be in the data section*/
	if (*header->map_off != 0){
		if (*header->map_off < *header->data_off) fprintf(stderr, "Warning: Map offset not in the Data section\n");
		
		u4 mapsize = (u4 *)*(fileinmemory + *header->map_off);
		put_pixels (&dexpng, *header->map_off ,mapsize*sizeof(map_item_struct)+sizeof(u4), 0,0,255);  // map -- blue
	}


    u2 strptr = sizeof(string_id_struct);

	/* Print the string part of the header */
	put_pixels ( &dexpng,*header->string_ids_off,*header->string_ids_size*strptr , 0,109,44);  // string_ids  -- darkgreen
	put_pixels( &dexpng, *header->type_ids_off, *header->type_ids_size*sizeof(type_id_struct), 44,162,95); // type_ids -- green
	put_pixels( &dexpng, *header->proto_ids_off, *header->proto_ids_size*sizeof(proto_id_struct), 102,194,164); // proto ids -- greenblue
	put_pixels( &dexpng, *header->field_ids_off, *header->field_ids_size*sizeof(field_id_struct), 153,216,201); // fields -- aquamarine  
    put_pixels( &dexpng, *header->method_ids_off, *header->method_ids_size*sizeof(method_id_struct), 204,236,230); // Method ids  -- bluegreen 
    put_pixels( &dexpng, *header->class_defs_off, *header->class_defs_size*sizeof(class_def_struct), 237,248,251); // class defs  

    // Color the strings
    int old = 0;
    int order;
    for (i= 0; i < *header->string_ids_size; i++) {
        string_id_list = (struct string_id_struct *) (fileinmemory + *header->string_ids_off + strptr * i); 
        if (*header->string_ids_off > old) order=1; else order =0;
        old = *header->string_ids_off;
		ColorStrings(&dexpng, fileinmemory, *string_id_list->string_data_off, order);
	}

    //Color the prototypes parameters
    for (i= 0; i < *header->proto_ids_size; i++) {
        proto_id_list = (struct proto_id_struct *) (fileinmemory + *header->proto_ids_off + sizeof(proto_id_struct) *i);
        if (*proto_id_list->parameters_off != 0) {  // It contains parameters ...
				u4 listsize = (u4 *)*(fileinmemory + *proto_id_list->parameters_off);
				put_pixels (&dexpng, *proto_id_list->parameters_off ,listsize*sizeof(type_id_struct)+sizeof(u4), 0,100,255);  // prototype parameters
			}
	}
	
	// Working with the classes
	
    for (i= 0; i < *header->class_defs_size; i++) {
        class_def_list = (struct class_def_struct *) (fileinmemory + *header->class_defs_off + sizeof(class_def_struct) *i);
		// -- interfaces
        if (*class_def_list->interfaces_off != 0) {  // It contains interfaces ...
				u4 listsize = (u4 *)*(fileinmemory + *class_def_list->interfaces_off);
				put_pixels (&dexpng, *class_def_list->interfaces_off ,listsize*sizeof(type_id_struct)+sizeof(u4), 0,150,255);  // class interfaces
		}
		// -- annotations
        if (*class_def_list->annotations_off != 0) {  // It contains interfaces ...
				annotations_directory_list = (annotations_directory_item_struct *) (fileinmemory + *class_def_list->annotations_off);
				u4 listsize = sizeof(annotations_directory_item_struct) + *annotations_directory_list->fields_size * sizeof(u4)*2;
				listsize += (*annotations_directory_list->annotated_methods_size * sizeof(u4))*2;
				listsize += (*annotations_directory_list->annotated_parameters_size * sizeof(u4))*2;
				put_pixels (&dexpng, *class_def_list->annotations_off ,listsize+sizeof(u4), 155,0,175);  // annotations
			}
		// TODO : work with the offsets inside the annotations 
		// -- class_data
		if (*class_def_list->class_data_off != 0) {  // It contains data, that means not interface.
				Analize_class_data(&dexpng, fileinmemory, *class_def_list->class_data_off); // This is a dynamic structure
			}
		// -- static_values
		if (*class_def_list->static_values_off != 0) {  // Offset to the list of initial values for static fields
				//encoded_array format  size=uleb128 + encoded_values[size]
				Analyze_encoded_value(&dexpng, fileinmemory, *class_def_list->static_values_off); // This is a dynamic structure
		}
	}

	save_ppm_to_file (&dexpng, outputname);
	
	free(fileinmemory);
	free(dexpng.pixels);
	free(outputname);
	return 0;
}
