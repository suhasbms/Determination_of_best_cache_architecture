#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#pragma align 16

#define MAX_LINES 131072
#define MAX_WAYS 16
#define MAX_WRITE_STRATEGIES 3
#define MAX_BURST_LENGTH 8
#define S 262144
#define ADDRESS_LINES 24
#define WAY_NOT_FOUND -1

#define SYMMETRIC_MATRIX 256

#define WB 0
#define WTA 1
#define WTNA 2

bool valid[MAX_LINES][MAX_WAYS];
bool dirty[MAX_LINES][MAX_WAYS];
uint8_t lru[MAX_LINES][MAX_WAYS];
uint16_t tag[MAX_LINES][MAX_WAYS];

//COUNTERS
uint64_t total_bytes_read;
uint64_t total_bytes_written;
//Read counters
uint64_t read_memory_count;
uint64_t read_cache_count;
uint64_t read_write_back_count;
uint64_t read_replace_count;
uint64_t read_memory_to_cache_count;
uint64_t read_cache_to_cpu_count;
uint64_t read_hit_count;
uint64_t read_miss_count;
//Write counters
uint64_t write_memory_count;
uint64_t write_miss_dirty_count;
uint64_t write_miss_replace_count;
uint64_t write_cache_count;
uint64_t write_through_memory;
uint64_t write_hit_count;
uint64_t write_miss_count;
uint64_t flush_counter;

uint8_t blocks;
uint8_t s;
uint8_t n;
uint8_t b;
uint8_t l;
uint8_t t;
uint32_t max_lines_for_bl_ways;

uint8_t instant_number_of_ways, instant_burst_length;
uint8_t write_strategy;

//Input Matrix varibles
double A[SYMMETRIC_MATRIX][SYMMETRIC_MATRIX];
double temp_A[SYMMETRIC_MATRIX][SYMMETRIC_MATRIX];
double pivot[SYMMETRIC_MATRIX][SYMMETRIC_MATRIX];
double P[SYMMETRIC_MATRIX];
double B[SYMMETRIC_MATRIX];
double X[SYMMETRIC_MATRIX];

void initialize_cache(uint8_t burst_length, uint8_t ways)
{
	uint32_t temp_line;
	uint8_t temp_way;

	blocks = burst_length * 2;
	b = log(blocks) / log(2);
	n = log(ways) / log(2);
	max_lines_for_bl_ways = pow(2, (s - b - n));
	l = log(max_lines_for_bl_ways) / log(2);
	t = ADDRESS_LINES - b - l;


	for (temp_line = 0; temp_line < max_lines_for_bl_ways; temp_line++)
	{

		for (temp_way = 0; temp_way < ways; temp_way++)
		{
			valid[temp_line][temp_way] = false;
			dirty[temp_line][temp_way] = false;
			lru[temp_line][temp_way] = temp_way;
		}
	}

	//clear performance counters
	total_bytes_read = 0;
	total_bytes_written = 0;

	//Read counters
	read_memory_count = 0;
	read_cache_count = 0;
	read_write_back_count =0;
	read_replace_count = 0;
	read_memory_to_cache_count = 0;
	read_cache_to_cpu_count = 0;
	read_hit_count = 0;
	read_miss_count = 0;

	//Write counters
	write_memory_count = 0;
	write_miss_dirty_count = 0;
	write_miss_replace_count = 0;
	write_cache_count = 0;
	write_through_memory = 0;
	write_hit_count = 0;
	write_miss_count = 0;

	flush_counter = 0;
}

uint32_t get_line(uint32_t add)
{
	uint32_t temp_line;
	add = add & 0x00FFFFFF;
	temp_line = (add >> b);
	temp_line = temp_line & (max_lines_for_bl_ways - 1);
	return (temp_line);
}

uint16_t get_tag(uint32_t add)
{
	uint16_t temp_tag;
	add = add & 0x00FFFFFF;
	temp_tag = add >> (b + l);
	return (temp_tag);
}

uint8_t find_oldest_lru_and_return_way(uint32_t add)
{
	uint32_t temp_line;
	uint8_t each_way = 0;
	temp_line = get_line(add);
	for (each_way = 0; each_way < instant_number_of_ways; each_way++)
	{
		if (lru[temp_line][each_way] == (instant_number_of_ways - 1))
		{
			return each_way;
		}
	}
}

void update_lru_age_all_with_line_way(uint32_t temp_line, uint8_t temp_way)
{
	uint8_t each_way;
	for (each_way = 0; each_way < instant_number_of_ways; each_way++)
	{
		if (each_way == temp_way)
		{
			for (uint8_t i = 0; i < instant_number_of_ways; i++)
			{
				if (lru[temp_line][i] < lru[temp_line][temp_way])
				{
					lru[temp_line][i]++;
				}
			}
			lru[temp_line][temp_way] = 0;
			break;
		}
	}
}

void create_cholesky_matrix()		//credits Math Resource youtube channel - https://www.youtube.com/watch?v=gFaOa4M12KU
{
	//Creating an upper triangular matrix and a pivot matrix(diagonal matrix)
	for (uint16_t m = 0; m < SYMMETRIC_MATRIX; m++)
	{
		for (uint16_t n = 0; n < SYMMETRIC_MATRIX; n++)
		{
			if (m >= n)
				A[m][n] = m + n + 1;
			if (m == n)
				pivot[m][n] = pow(m + 1, 2);
		}
	}

	//Multiplying upper triangular matrix with pivot matrix
	for (uint16_t m = 0; m < SYMMETRIC_MATRIX; m++)
	{
		for (uint16_t n = 0; n < SYMMETRIC_MATRIX; n++)
		{
			temp_A[m][n] = 0;
			for (uint16_t k = 0; k < 256; k++)
				temp_A[m][n] += A[m][k] * pivot[k][n];
		}
	}

	//Making the adding the upper triangular matrix and lower matrix and making it symmetrical
	for (uint16_t m = 0; m < SYMMETRIC_MATRIX; m++)
	{
		for (uint16_t n = 0; n < SYMMETRIC_MATRIX; n++)
		{
			if (m == n)
				temp_A[m][n] = temp_A[m][n] * 2;
			if (m < n)
				temp_A[m][n] = temp_A[n][m];
		}
	}

	for (uint16_t m = 0; m < SYMMETRIC_MATRIX; m++)
	{
		for (uint16_t n = 0; n < SYMMETRIC_MATRIX; n++)
		{
			A[m][n] = temp_A[m][n];
		}
	}

	//Creating value B for least square caculation
	for (uint16_t m = 0; m < SYMMETRIC_MATRIX; m++)
	{
		B[m] = m + 10000;
	}

}

int find_tag(uint32_t line_number, uint16_t tag_number)
{
	for (uint8_t i = 0; i < instant_number_of_ways; i++)
	{
		if ((tag[line_number][i] == tag_number) && (valid[line_number][i] == true))
		{
			return i;
		}
	}
	return WAY_NOT_FOUND;

}

void flush_cache()
{
	for (uint32_t i = 0; i < max_lines_for_bl_ways; i++)
	{
		for (uint8_t j = 0; j < instant_number_of_ways; j++)
		{
			if (dirty[i][j] == 1)
			{
				flush_counter++;
				dirty[i][j] = 0;
			}
		}
	}
}

void set_tag(uint32_t temp_line, uint8_t temp_way, uint16_t temp_tag)
{
	tag[temp_line][temp_way] = temp_tag;
}

void read_mem_to_cache()
{
	read_memory_to_cache_count++;
}

void read_cache_to_cpu()
{
	read_cache_to_cpu_count++;
}

void write_back_to_memory()
{
	read_write_back_count++;
}

void replace_data_in_cache()
{
	read_replace_count++;
}

void read_cache(uint32_t add)
{
	uint32_t temp_line;
	uint16_t temp_tag;
	int temp_way;
	bool temp_hit;

	read_cache_count++;

	temp_line = get_line(add);
	temp_tag = get_tag(add);
	temp_way = find_tag(temp_line, temp_tag);
	temp_hit = (temp_way != WAY_NOT_FOUND);

	if (!temp_hit)
	{
		temp_way = find_oldest_lru_and_return_way(add);
		if (dirty[temp_line][temp_way])
		{
			write_back_to_memory();
			replace_data_in_cache();
			dirty[temp_line][temp_way] = 0;
		}
		valid[temp_line][temp_way] = 0;
		set_tag(temp_line, temp_way, temp_tag);
		read_mem_to_cache();
		valid[temp_line][temp_way] = 1;
		update_lru_age_all_with_line_way(temp_line, temp_way);
	}

	update_lru_age_all_with_line_way(temp_line, temp_way);
	read_cache_to_cpu();

	if (temp_hit)
	{
		read_hit_count++;
	}
	else read_miss_count++;
}

void read_memory(void* pmemory, uint32_t size)
{
	read_memory_count++;
	int32_t last_line = -1;
	uint32_t add = (uint32_t)pmemory;
	uint32_t temp_line;

	for (uint8_t i = 0; i < size; i++)
	{
		temp_line = get_line(add);
		if (temp_line != last_line)
		{
			read_cache(add);
			last_line = temp_line;
		}
		add++;
	}
	total_bytes_read += size;
}

void replace_the_data_in_cache()
{
	write_miss_dirty_count++;
	write_miss_replace_count++;
}

void write_cache(uint32_t add)
{
	uint32_t temp_line;
	uint16_t temp_tag;
	int temp_way;
	bool temp_hit;

	temp_line = get_line(add);
	temp_tag = get_tag(add);
	temp_way = find_tag(temp_line, temp_tag);
	temp_hit = (temp_way != WAY_NOT_FOUND);

	if ((!temp_hit) && (write_strategy != WTNA))
	{
		temp_way = find_oldest_lru_and_return_way(add);

		if (dirty[temp_line][temp_way])
		{
			replace_the_data_in_cache();
			dirty[temp_line][temp_way] = 0;
		}

		valid[temp_line][temp_way] = 0;

		set_tag(temp_line, temp_way, temp_tag);

		valid[temp_line][temp_way] = 1;

		update_lru_age_all_with_line_way(temp_line, temp_way);
	}

	if (write_strategy == WB)
	{
		dirty[temp_line][temp_way] = 1;
	}

	if (temp_hit || (write_strategy != WTNA))
	{
		update_lru_age_all_with_line_way(temp_line, temp_way);
		write_cache_count++;
	}

	if ((write_strategy == WTA) || (write_strategy == WTNA))
	{
		write_through_memory++;
	}

	if (temp_hit)
	{
		write_hit_count++;
	}
	else write_miss_count++;


}

void write_memory(void* pmemory, uint32_t size)
{
	int32_t last_line = WAY_NOT_FOUND;
	uint32_t temp_line;
	uint32_t add = (uint32_t)pmemory;

	write_memory_count++;

	for (uint8_t i = 0; i < size; i++)
	{
		temp_line = get_line(add);
		if (temp_line != last_line)
		{
			write_cache(add);
			last_line = temp_line;
		}
		add++;
	}

	total_bytes_written += size;

}

void choldc(double a[SYMMETRIC_MATRIX][SYMMETRIC_MATRIX], int n, double p[SYMMETRIC_MATRIX])
{
	//choldc
	int i, j, k;
	double sum;

	write_memory(&i, sizeof(int));
	read_memory(&n, sizeof(int));
	for (i = 0; i < n; i++)
	{
		read_memory(&i, sizeof(int));
		write_memory(&j, sizeof(int));
		read_memory(&n, sizeof(int));
		for (j = i; j < n; j++)
		{
			read_memory(&i, sizeof(int));
			read_memory(&j, sizeof(int));
			read_memory(&a[i][j], sizeof(double));
			write_memory(&sum, sizeof(double));
			write_memory(&k, sizeof(int));
			for (sum = a[i][j], k = i - 1; k >= 0; k--)
			{
				read_memory(&sum, sizeof(double));
				read_memory(&i, sizeof(int));
				read_memory(&k, sizeof(int));
				read_memory(&a[i][k], sizeof(double));
				read_memory(&j, sizeof(int));
				read_memory(&a[j][k], sizeof(double));
				write_memory(&sum, sizeof(double));
				sum -= a[i][k] * a[j][k];

				read_memory(&k, sizeof(int));
				write_memory(&k, sizeof(int));

			}

			read_memory(&i, sizeof(int));
			read_memory(&j, sizeof(int));
			if (i == j)
			{
				read_memory(&sum, sizeof(double));
				if (sum <= 0)
				{
					printf("Hmmmmmm!");
				}

				read_memory(&sum, sizeof(double));
				read_memory(&i, sizeof(int));
				write_memory(&p[i], sizeof(double));
				p[i] = sqrt(sum);

			}
			else
			{
				read_memory(&sum, sizeof(double));
				read_memory(&i, sizeof(int));
				read_memory(&p[i], sizeof(double));
				read_memory(&j, sizeof(int));
				write_memory(&a[j][i], sizeof(double));
				a[j][i] = sum / p[i];
			}

			read_memory(&j, sizeof(int));
			write_memory(&j, sizeof(int));
			read_memory(&n, sizeof(int));
		}
		read_memory(&i, sizeof(int));
		write_memory(&i, sizeof(int));
		read_memory(&n, sizeof(int));
	}
}

void cholsl(double a[SYMMETRIC_MATRIX][SYMMETRIC_MATRIX], int n, double p[SYMMETRIC_MATRIX], double b[SYMMETRIC_MATRIX], double x[SYMMETRIC_MATRIX])
{
	int i, k;
	double sum;

	write_memory(&i, sizeof(int));
	read_memory(&n, sizeof(int));
	for (i = 0; i < n; i++)
	{
		read_memory(&i, sizeof(int));
		read_memory(&b[i], sizeof(double));
		write_memory(&sum, sizeof(double));
		sum = b[i];

		read_memory(&i, sizeof(int));
		write_memory(&k, sizeof(int));
		for (k = i - 1; k >= 0; k--)
		{
			read_memory(&sum, sizeof(double));
			read_memory(&i, sizeof(int));
			read_memory(&k, sizeof(int));
			read_memory(&a[i][k], sizeof(double));
			read_memory(&x[k], sizeof(double));
			write_memory(&sum, sizeof(double));
			sum -= a[i][k] * x[k];

			read_memory(&k, sizeof(int));
			write_memory(&k, sizeof(int));
		}

		read_memory(&i, sizeof(int));
		read_memory(&p[i], sizeof(double));
		read_memory(&sum, sizeof(double));
		write_memory(&x[i], sizeof(double));
		x[i] = sum / p[i];

		read_memory(&i, sizeof(int));
		write_memory(&i, sizeof(int));
		read_memory(&n, sizeof(int));
	}

	read_memory(&n, sizeof(int));
	write_memory(&i, sizeof(int));
	for (i = n - 1; i >= 0; i--)
	{
		read_memory(&i, sizeof(int));
		read_memory(&x[i], sizeof(double));
		write_memory(&sum, sizeof(double));
		sum = x[i];

		read_memory(&i, sizeof(int));
		read_memory(&n, sizeof(int));
		write_memory(&k, sizeof(int));
		for (k = i + 1; k < n; k++)
		{
			read_memory(&sum, sizeof(double));
			read_memory(&k, sizeof(int));
			read_memory(&i, sizeof(int));
			read_memory(&a[k][i], sizeof(double));
			read_memory(&x[k], sizeof(double));
			write_memory(&sum, sizeof(double));
			sum -= a[k][i] * x[k];

			read_memory(&k, sizeof(int));
			write_memory(&k, sizeof(int));
			read_memory(&n, sizeof(int));
		}

		read_memory(&i, sizeof(int));
		read_memory(&p[i], sizeof(double));
		read_memory(&sum, sizeof(double));
		write_memory(&x[i], sizeof(double));
		x[i] = sum / p[i];

		read_memory(&i, sizeof(int));
		write_memory(&i, sizeof(int));
	}
}

int write_to_text(FILE *f)
{
	fprintf(f, "%u\t", write_strategy);
	fprintf(f, "%u\t", instant_number_of_ways);
	fprintf(f, "%u\t", instant_burst_length);

	fprintf(f, "%lu\t", total_bytes_read);
	fprintf(f, "%lu\t", total_bytes_written);

	fprintf(f, "%lu\t", read_memory_count);
	fprintf(f, "%lu\t", read_cache_count);
	fprintf(f, "%lu\t", read_write_back_count);
	fprintf(f, "%lu\t", read_replace_count);
	fprintf(f, "%lu\t", read_memory_to_cache_count);
	fprintf(f, "%lu\t", read_cache_to_cpu_count);
	fprintf(f, "%lu\t", read_hit_count);
	fprintf(f, "%lu\t", read_miss_count);

	fprintf(f, "%lu\t", write_memory_count);
	fprintf(f, "%lu\t", write_miss_dirty_count);
	fprintf(f, "%lu\t", write_miss_replace_count);
	fprintf(f, "%lu\t", write_cache_count);
	fprintf(f, "%lu\t", write_through_memory);
	fprintf(f, "%lu\t", write_hit_count);
	fprintf(f, "%lu\t", write_miss_count);

	fprintf(f, "%lu\t\n", flush_counter);
}

void main()
{
	
	FILE *fp;
	s = log(S) / log(2);
	fopen_s(&fp,"Text.txt", "w+");
	fprintf(fp, "Write Strategy\tNumber of ways\tBurst Length\tTotal Bytes read\tTotal Bytes Written\tRead Memory Count\tRead Cache Count\tRead Write Back Count\tRead Replace Count\tRead Memory to cache Count\tRead Cache to CPU Count\tRead Hit Count\tRead Miss Count\tWrite Memory Count\tWrite Miss Dirty Count\tWrite Miss Replace Count\tWrite Cache count\tWrite throught Memory\tWrite Hit Count\tWrite Miss Count\tFlush Count\n");
	
	for (write_strategy = WB; write_strategy < MAX_WRITE_STRATEGIES; write_strategy++)
	{
		for (instant_number_of_ways = 1; instant_number_of_ways <= MAX_WAYS; instant_number_of_ways *= 2)
		{
			for (instant_burst_length = 1; instant_burst_length <= MAX_BURST_LENGTH; instant_burst_length *= 2)
			{
				initialize_cache(instant_burst_length, instant_number_of_ways);
				create_cholesky_matrix();
				//choldc
				choldc(A, SYMMETRIC_MATRIX, P);
				//cholsl
				cholsl(A, SYMMETRIC_MATRIX, P, B, X);
				//Copy cache to memory at the end(Burst)
				flush_cache();
				write_to_text(fp);			
			}
		}
	}

	fclose(fp);
   	while (1);
}