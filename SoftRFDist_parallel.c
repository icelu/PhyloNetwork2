/* Copyright:  Bingxin Lu, National University of Singapore, 2016
 * This is a parallel program for computing the Soft Robinson-Foulds cluster distance between two phylogenetic networks.
 * The input to the program includes two phylogenetic networks.
 * The input network has the following property:
 *   -- each tree node has an indegree of 1;
 *   -- each reticulation node must an out-degree 1;
 *   -- only one root and no node has both in- and out-degree > 1
 *
 *   The compiling command:  gcc -fopenmp -o psrfd SoftRFDist_parallel.c
 *   The run command:        ./psrfd <network_file1_name> <network_file2_name>

 *   The network is represented as a set of edges, each on
 *   a line. For example, this is a file of the input network
 *      1 2
 *      1 3
 *      3 4
 *      4 5
 *      2 6
 *      3 6
 *      6 leaf1
 *      5 leaf2
 *      5 leaf3
 *      4 leaf4
 *  Another important assumption is that
 * 	the network has 350 nodes and 500 edges at most and each node
 *  has at most degree 20. But this can be adjusted by
 *  resetting constants MAXDEGREE, MAXSIZE and MAXEDGE
 */


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

#define max(a,b) ({ __typeof__ (a) _a = (a); __typeof__ (b) _b = (b); _a > _b ? _a : _b; })

#define ROOT 0
#define TREE 1
#define RET 2
#define LEAVE 3
#define INNER 4
#define CROSS 5
#define REVISED 6
#define MAXDEGREE 20
#define MAXRET 50
#define MAXSIZE  350
#define MAXEDGE  500

struct lnode {
	int leaf;
	struct lnode *next;
};

struct arb_tnode { /* arbitrary tree node */
	int label;
	int flag;
	int no_children;
	struct arb_tnode *child[MAXDEGREE];
};

struct components {
	int ret_node;
	int inner;
	int size;	// used for copying network with array
	int no_tree_node; // used for checking degenerate case
	struct arb_tnode *tree_com;
	struct components *next;
};

struct network {
	int root;
	int n_r;
	int n_l;
	int no_nodes;
	char **node_strings;
	int *net_edges;
	struct lnode **child_array;
	struct lnode **parent_array;
	int *lf_below; /* what is the leaf below a reticulation */
	int *inner_flag; /* whether a ret is inner or cross */
	int *super_deg;
	int *node_type;
	int *r_nodes;
	struct components *all_cps;
};

// Used to keep track of sorted index
struct temp_node{
	int pnode;
	int value;
	int index;
};

int tnode_comparator(const void *v1, const void *v2)
{
    const struct temp_node *p1 = (struct temp_node *)v1;
    const struct temp_node *p2 = (struct temp_node *)v2;
    if (p1->value > p2->value)
        return -1;
    else if (p1->value < p2->value)
        return +1;
    else
        return 0;
}


/* count the number of 1 in the binary representation of x. */
int pop(unsigned int x) {
	int n;
	n = 0;
	while (x != 0) {
		n = n + 1;
		x = x & (x - 1);
	}
	return n;
}

/*
 * from http://stackoverflow.com/questions/31577866/c-programming-convert-integer-to-binary-array
 */
void int_to_bin_digit(unsigned int in, int count, int* out) {
	unsigned int mask = 1U << (count - 1);
	int i;
	for (i = 0; i < count; i++) {
		out[i] = (in & mask) ? 1 : 0;
		in <<= 1;
	}
}


struct lnode *ListExtend(struct lnode *list, int lf) {
	struct lnode *p, *q;
	p = (struct lnode*) malloc(sizeof(struct lnode));
	p->leaf = lf;
	p->next = NULL;
	if (list == NULL)
		list = p;
	else {
		q = list;
		while (q->next != NULL)
			q = q->next;
		q->next = p;
	}
	return list;
}

struct arb_tnode *Search_Revised(struct arb_tnode *tree, int node) {
	struct arb_tnode *p;
	int i, deg;

	if (tree != NULL) {
		if (tree->label == node)
			return tree;
		else {
			deg = tree->no_children;
			p = NULL;
			for (i = 0; i < deg; i++) {
				p = Search_Revised((tree->child)[i], node);
				if (p != NULL)
					return p;
			}
		}
	}
	return NULL;
}

int Is_In(int elt, int ambig[], int n) {
	int i;

	for (i = 0; i < n; i++)
		if (elt == ambig[i])
			return 1;
	return -1;
}

int Is_In_Str(char* node, char* leaves[], int n) {
	int i;

	for (i = 0; i < n; i++)
		if (strcmp(node, leaves[i]) == 0)
			return 1;
	return 0;
}

/* mark forbidden nodes in the multi-labelled tree */
void Mark_Revised(struct arb_tnode *tree, int leaf, int *no_mark) {
	int i, deg, x, y;

	if (tree == NULL)
		return;
	else {
		deg = tree->no_children;
		if (deg == 0 && tree->label == leaf) {
			tree->flag = 1;
			*no_mark += 1;
			return;
		}
		x = 0;
		y = -1;
		for (i = 0; i < deg; i++) {
			if (Search_Revised((tree->child)[i], leaf) != NULL) {
				x = x + 1;
				y = i;
			}
		}
		if (x == 1) {
			tree->flag = 1;
			*no_mark += 1;
			Mark_Revised((tree->child)[y], leaf, no_mark);
		} else if (x > 1) {
			tree->flag = 1;
			*no_mark += 1;
			return;
		} else
			return;
	}
}

void Find_Vmax(struct arb_tnode *tree, int vmax[], int *no_vmax) {
	int i, k, y, deg;

	if (tree == NULL)
		return;
	else {
		if (tree->flag == 1) {
			deg = tree->no_children;
			for (i = 0; i < deg; i++) {
				if ((tree->child)[i]->flag == 0) {
					y = 0;
					for (k = 0; k < *no_vmax; k++) {
						if (vmax[k] == (tree->child)[i]->label) {
							y = -1;
							break;
						}
					}
					if (y == 0) {
						vmax[*no_vmax] = (tree->child)[i]->label;
						*no_vmax = 1 + *no_vmax;
					}
				} else {
					Find_Vmax((tree->child)[i], vmax, no_vmax);
				}
			}
		}
	}
	return;
}

int Count_Child(struct lnode *p) {
	if (p == NULL)
		return 0;
	else
		return 1 + Count_Child(p->next);
}

/* decide whether x is a child of y */
int Is_Child(int x, int y, struct lnode *child_array[]) {
	struct lnode * c;

	c = child_array[y];
	while (c != NULL) {
		if (c->leaf == x)
			return 1;
		c = c->next;
	}
	return 0;
}

void Build_Comp_Revised(struct arb_tnode *p, struct lnode *child_array[],
		int node_type[], int no_nodes, int *size, int *no_tree_node) {
	int i, j;
	struct tnode *x, *y;
	struct lnode *qq;

	if (p == NULL)
		return;
	if (node_type[p->label] == LEAVE){
		return;
	}
	if (node_type[p->label] == RET)
		return;

	if (node_type[p->label] == TREE || node_type[p->label] == ROOT) {
		p->no_children = Count_Child(child_array[p->label]);
		qq = child_array[p->label];

		for (i = 0; i < MAXDEGREE; i++)
			(p->child)[i] = NULL;

		for (i = 0; i < p->no_children; i++) {
			// printf("node_type %d -- %d\n",qq->leaf, node_type[qq->leaf]);
			if (RET != node_type[qq->leaf]) {
				*no_tree_node += 1;
			}
			*size += 1;
			(p->child)[i] = (struct arb_tnode *) malloc(
					sizeof(struct arb_tnode));

			((p->child)[i])->label = qq->leaf;
			((p->child)[i])->flag = 0;
			((p->child)[i])->no_children = 0;
			qq = qq->next;
			Build_Comp_Revised((p->child)[i], child_array, node_type, no_nodes,
					size, no_tree_node);
		}
	}
	return;
}



void Print_Revised(struct arb_tnode *tree, char *node_strings[]) {
	int deg, i;
	if (tree != NULL) {
		printf("%s, flag %d\n", node_strings[tree->label], tree->flag);
		deg = tree->no_children;
		for (i = 0; i < deg; i++) {
			Print_Revised((tree->child)[i], node_strings);
		}
	} else
		return;
}

void Print_Comp_Revised(struct arb_tnode *tree, char *node_strings[]) {
	int i;

	if (tree != NULL) {
		if (tree->label >= 0) {
			printf("    %s: ", node_strings[tree->label]);
			if (tree->no_children > 0) {
				for (i = 0; i < tree->no_children; i++) {
					printf(" (%s ", node_strings[(tree->child[i])->label]);
				}
			}
			printf("\n");
			for (i = 0; i < tree->no_children; i++)
				Print_Comp_Revised((tree->child)[i], node_strings);
		}
	} else {
		printf("     empty\n");
	}
}

int Is_In_Comp(struct arb_tnode *tree, int node) {
	int i, k;

	k = 0;
	if (tree != NULL) {
		if (tree->no_children == 0) {
			if (node == tree->label)
				k = 1;
			else
				k = 0;
		} else {
			for (i = 0; i < tree->no_children; i++) {
				k = k + Is_In_Comp((tree->child)[i], node);
			}
		}
	} else
		k = 0;

	if (k > 0)
		return 1;
	else
		return 0;
}

void Initiallize(struct arb_tnode *tree) {
	int i, deg;

	if (tree != NULL) {
		tree->flag = 0;
		deg = tree->no_children;
		for (i = 0; i < deg; i++)
			Initiallize((tree->child)[i]);
	} else
		return;
}

void PostTrans_Revised(struct arb_tnode *tree, struct arb_tnode *postList[],
		int *n) {
	int i, deg;
	if (tree != NULL) {
		deg = tree->no_children;
		if (deg > 0) {
			for (i = 0; i < deg; i++)
				PostTrans_Revised((tree->child)[i], postList, n);
		}
		postList[*n] = tree;
		*n += 1;
	}
}

void PrintList_Revised(struct arb_tnode *postList[], char *names[], int no) {
	int i;
	for (i = 0; i < no; i++) {
		printf("%s ", names[(postList[i])->label]);
	}
	printf("\n");
}

int Check_List(int list_a[], int no, int b) {
	int i;
	for (i = 0; i < no; i++) {
		if (list_a[i] == b)
			return i;
	}
	return -1;
}

/*
 check whether the set of input leaves is a cluster of some node a tree component
 */
int DProgram_Revised(char *node_strings[], struct arb_tnode *super_t,
		int n_embed, int map_nodes[][MAXSIZE], int vmax[], int no_vmax,
		int input_leaves[], int node_type[]) {
	int i, j, k, x;
	struct arb_tnode *p;
	/* each node in the cluster corresponds to a column */
	/* each node in V_max corresponds to a row */
	for (j = 0; j < no_vmax; j++) {
		k = 0;
		p = Search_Revised(super_t, vmax[j]);
		for (i = 0; i < n_embed; i++) {
			x = Is_Below(p, input_leaves[i], node_type);
			if (x == 1) {
				map_nodes[j][i] = 1;
				k += 1;
			}
		}
		/* B is a cluster of some node if there is one row of 1 */
		if (k == n_embed) {
			return vmax[j];
		}
	}
	return -1;
}

int Check_Name(char *node_strings[], int no_nodes, char *str1) {
	int i;

	if (str1 == NULL)
		return -1;
	for (i = 0; i < no_nodes; i++) {
		if (strcmp(str1, node_strings[i]) == 0)
			return i;
	}
	return -1;
}


void Add_Component(struct components *com_ptr, int ret, int child, int inn, int node_type[]) {
	struct components *p;
	int k;

	p = com_ptr;
	while (p->next != NULL) {
		p = p->next;
	}

	p->next = (struct components *) malloc(sizeof(struct components));
	(p->next)->ret_node = ret;
	(p->next)->inner = inn;
	(p->next)->size = 1;
	(p->next)->tree_com = (struct arb_tnode *) malloc(sizeof(struct arb_tnode));
	((p->next)->tree_com)->label = child;
	if(node_type[child]==RET){
		(p->next)->no_tree_node = 0;
	}else{
		(p->next)->no_tree_node = 1;
	}
	((p->next)->tree_com)->no_children = 0;
	((p->next)->tree_com)->flag = 0;
	for (k = 0; k < MAXDEGREE; k++)
		(((p->next)->tree_com)->child)[k] = NULL;
	(p->next)->next = NULL;
}


/* if ret x is right below ret y as an inner ret */
int Is_Below_revised(int ret_x, int y, struct lnode *parent_array[],
		int node_type[]) {
	int i, j, p, v = 0;
	struct lnode *q;

	q = parent_array[ret_x];
	while (q != NULL) {
		p = q->leaf;
		while (node_type[p] == TREE) {
			p = (parent_array[p])->leaf;
		}
		if (p == y) {
			v = 1;
			break;
		}
		q = q->next;
	}
	if (v == 1)
		return 1;
	else
		return -1;
}

/* if a leaf y is below a node p */
int Is_Below(struct arb_tnode *p, int y, int node_type[]) {
	int i, x;

	x = p->label;
	if (node_type[x] == LEAVE) {
		if (x == y) {
			return 1;
		} else {
			return 0;
		}
	}

	for (i = 0; i < p->no_children; i++) {
		if (Is_Below((p->child)[i], y, node_type) == 1) {
			return 1;
		}
	}

	return 0;
}

/*determine if all the parents of node is in a component */
int Is_Inner_Revised(int node, struct lnode *parent_array[], int node_type[],
		int no_nodes) {
	int f, g;
	struct lnode *p, *q, *y;

	f = (parent_array[node])->leaf;
	q = (parent_array[node])->next;
	while (node_type[f] == TREE) {
		p = parent_array[f];
		f = p->leaf;
	}

	/* at this stage f is the root of network or a reticulation node */
	while (q != NULL) {
		g = q->leaf;
		while (node_type[g] == TREE) {
			y = parent_array[g];
			g = y->leaf;
		}
		if (f != g)
			return CROSS;
		q = q->next;
	}
	return INNER;
}


int Is_Tree_Component(int rnode, int node_type[], struct lnode *child_array[]){
	struct lnode *p;
	p = child_array[rnode];
	int res=0;
	while (p != NULL) {
		if (node_type[p->leaf] == LEAVE){
		}
		else if (node_type[p->leaf] == RET){ // There is a reticulate node below current reticulate node
			return 1;
		}
		else // if(node_type[p->leaf] == TREE)
		{
			res= Is_Tree_Component(p->leaf, node_type, child_array);
			if (res==1) return 1;
		}
		p = p->next;
	}
		return res;
}


void Count_Ret_Child(int rnode, int *count, int *flag, int *size, int n_r, int orig_rnodes[], int node_type[], struct lnode *child_array[]){
	struct lnode *p;
	p = child_array[rnode];
	while (p != NULL) {
		if (node_type[p->leaf] == LEAVE){
			*size +=1;
		}
		else if (node_type[p->leaf] == RET){
			*count += 1;
			if (Is_In(p->leaf, orig_rnodes, n_r)==-1)
			{
				*flag+=1;
			}
		}
		else // if(node_type[p->leaf] == TREE)
		{
			*size +=1;
			Count_Ret_Child(p->leaf, count, flag, size, n_r, orig_rnodes, node_type, child_array);
		}
		p = p->next;
	}
		return;
}

int Is_Empty(int n_r, int r_nodes[]){
	int i;
	for (i = 0; i < n_r; i++) {
		if (r_nodes[i]!=-2) return 0;
	}
	return 1;
}

void Sort_Rets_By_Level(int orig_rnodes[], int r_nodes[], int n_r, struct lnode *child_array[],
		struct lnode *parent_array[], int node_type[], int no_nodes) {
	int i, j, u1, u2, x, y, node1, node2;
	int flag = 0;
	int count = 0;
	int k = 0;
	int size = 0;
	struct lnode *p;

	// Move reticulate nodes just above a single leaf to front
	j = 0;
	for (i = 0; i < n_r; i++) {
		flag = 0;
		if (orig_rnodes[i]==-2) continue;
		p = child_array[orig_rnodes[i]];
		while (p != NULL) {
			if (node_type[p->leaf] == LEAVE)
				p = p->next;
			else {
				flag = 1;	// There is a nonleaf below this ret node
				break;
			}
		}
		if (flag == 0) {
			r_nodes[j] = orig_rnodes[i];
			orig_rnodes[i] = -2;	// not consider this node later
			j = j + 1;
		}
	}

	// Moving reticulate nodes with only tree nodes
	for (i = 0; i < n_r; i++) {
		if (orig_rnodes[i]==-2) continue;
		flag =  Is_Tree_Component(orig_rnodes[i], node_type, child_array);
		if (flag == 0) {
			r_nodes[j] = orig_rnodes[i];
			orig_rnodes[i] = -2;
			j = j + 1;
		}
	}

	// Moving reticulate nodes one level higher
	while(Is_Empty(n_r, orig_rnodes)==0){
		struct temp_node level_ret[n_r]; 	// Temporily store all reticulate codes in the same level for sorting
		k=0;	// store the real size of the array
		for (i = 0; i < n_r; i++) {
			if (orig_rnodes[i]==-2) continue;
			count = 0;	// Count the number of reticulate children
			flag = 0;	// Count the number of reticulate children which have been resolved
			size = 0;
			Count_Ret_Child(orig_rnodes[i], &count, &flag, &size, n_r, orig_rnodes, node_type, child_array);
			if (flag > 0 && flag == count) {
				struct temp_node tnode;
				tnode.index = i;
				tnode.value = size;
				tnode.pnode = orig_rnodes[i];
				level_ret[k++] = tnode;
			}
		} // for loop -- finish one level
		qsort(level_ret, k, sizeof(struct temp_node), tnode_comparator);
		for (i = 0; i < k; i++){
			r_nodes[j++] = level_ret[i].pnode;
			orig_rnodes[level_ret[i].index] = -2;	//update later to avoid handling reticulate nodes at a higher level
		}
	}
}


/* replace a reticulation by a leaf */
/* leaf_set: stable leaves, no_lf: no. of stable leaves */
void Replace_Ret_Revised(struct arb_tnode *tree, int inner_flag[],
		int node_type[], int leaf_below[], int leaf_set[], int *no_lf,
		int ambig[], int *no_ambig, int optional[], int *no_opt,
		char *node_strings[], int *rpl_comp, int super_deg[]) {
	int i, k, j, x, y;

	if (tree == NULL)
		return;
	if (tree != NULL) {
		if (tree->no_children == 0) {
			if (node_type[tree->label] == LEAVE) {
				i = *no_lf;
				y = 0;

				for (k = 0; k < i; k++) {
					if (leaf_set[k] == tree->label) {
						y = -1;
						break;
					}
				}
				if (y == 0) {
					leaf_set[*no_lf] = tree->label;
					*no_lf = 1 + *no_lf;
				}
			} else if (node_type[tree->label] == RET) {
				if(leaf_below[tree->label] == -2) return;
				if (inner_flag[tree->label] == INNER) {
					x = tree->label;
					tree->label = leaf_below[x];
					rpl_comp[leaf_below[x]] = x;

					/* check if the node is recorded or not */
					i = *no_lf;
					y = 0;
					for (k = 0; k < i; k++) {
						if (leaf_set[k] == leaf_below[x]) {
							y = -1;
							break;
						}
					}
					if (y == 0 && tree->label >= 0) {
						leaf_set[*no_lf] = leaf_below[x];
						*no_lf = 1 + *no_lf;
					}

					/* check if the node is recored or not */
					i = *no_ambig;
					y = 0;
					for (k = 0; k < i; k++) {
						if (ambig[k] == leaf_below[x]) {
							y = -1;
							break;
						}
					}
					if (y == 0) {
						ambig[*no_ambig] = leaf_below[x];
						*no_ambig = 1 + *no_ambig;
					}
				} else if (inner_flag[tree->label] == CROSS) {
					x = tree->label;
					inner_flag[x] = REVISED;
					tree->label = leaf_below[x];
					rpl_comp[leaf_below[x]] = x;

					i = *no_opt;
					y = 0;
					for (k = 0; k < i; k++) {
						if (optional[k] == leaf_below[x]) {
							y = -1;
							break;
						}
					}
					if (y == 0) {
						optional[*no_opt] = leaf_below[x];
						*no_opt = 1 + *no_opt;
					}
				} else if (inner_flag[tree->label] == REVISED) {
					x = tree->label;
					tree->label = leaf_below[x];
					rpl_comp[leaf_below[x]] = x;

					if (super_deg[x] > 2) {
						i = *no_opt;
						y = 0;
						for (k = 0; k < i; k++) {
							if (optional[k] == leaf_below[x]) {
								y = -1;
								break;
							}
						}
						if (y == 0) {
							optional[*no_opt] = leaf_below[x];
							*no_opt = 1 + *no_opt;
						}
					} else {
						i = *no_ambig;
						y = 0;
						for (k = 0; k < i; k++) {
							if (ambig[k] == leaf_below[x]) {
								y = -1;
								break;
							}
						}
						if (y == 0) {
							ambig[*no_ambig] = leaf_below[x];
							*no_ambig = 1 + *no_ambig;
						}
					}
				}
			} /* ret case */
			return;
			/* non leaf */
		} else {
			for (i = 0; i < tree->no_children; i++) {
				Replace_Ret_Revised((tree->child)[i], inner_flag, node_type,
						leaf_below, leaf_set, no_lf, ambig, no_ambig, optional,
						no_opt, node_strings, rpl_comp, super_deg);
			}
			return;
		}
	} /* end non trivial case */

}

void List_Leaves_First(char *leave_names[], int node_type1[], int no1,
		int start1[], int end1[], int no_edges1) {
	int count, count1, i, j, x, y, k;
	char str1[50];

	count = 0;
	for (i = 0; i < no1; i++) {
		if (node_type1[i] == LEAVE) {
			count1 = node_type1[count];
			node_type1[count] = LEAVE;
			node_type1[i] = count1;
			strcpy(str1, leave_names[count]);
			k = strlen(leave_names[i]);
			free(leave_names[count]);
			leave_names[count] = (char *) malloc(k + 1);
			strcpy(leave_names[count], leave_names[i]);
			k = strlen(str1);
			free(leave_names[i]);
			leave_names[i] = (char *) malloc(k + 1);
			strcpy(leave_names[i], str1);
			x = -1;
			y = -1;
			for (j = 0; j < no_edges1; j++) {
				if (start1[j] == count) {
					if (x == -1)
						x = j;
					else
						y = j;
				}
			}
			start1[x] = i;
			start1[y] = i;
			x = -1;
			y = -1;
			for (j = 0; j < no_edges1; j++) {
				if (end1[j] == count)
					x = j;
				if (end1[j] == i)
					y = j;
			}
			if (x != -1)
				end1[x] = i;
			if (y != -1)
				end1[y] = count;
			count = count + 1;
		}
		/* if (i==3) break; */
	}
}

/* if any leaf is not in the network, report -1 */
int Move_Leaves_Front(char *ntk_names[], int no, int start[], int end[],
		int no_edges, char *leave_names[], int n_l) {
	char str1[20];
	int i, j, k, count;

	for (i = 0; i < n_l; i++) {
		count = 0;
		for (j = 0; j < no; j++) {
			if (strcmp(leave_names[i], ntk_names[j]) == 0) {
				strcpy(str1, ntk_names[i]);
				free(ntk_names[i]);
				k = strlen(ntk_names[j]);
				ntk_names[i] = (char *) malloc(k + 1);
				strcpy(ntk_names[i], ntk_names[j]);
				free(ntk_names[j]);
				k = strlen(str1);
				ntk_names[j] = (char *) malloc(k + 1);
				strcpy(ntk_names[j], str1);

				for (k = 0; k < no_edges; k++) {
					if (start[k] == i) {
						start[k] = -1;
					}
					if (start[k] == j) {
						start[k] = -2;
					}
					if (end[k] == i) {
						end[k] = -1;
					}
					if (end[k] == j) {
						end[k] = -2;
					}
				}

				for (k = 0; k < no_edges; k++) {
					if (start[k] == -1) {
						start[k] = j;
					}
					if (start[k] == -2) {
						start[k] = i;
					}
					if (end[k] == -1) {
						end[k] = j;
					}
					if (end[k] == -2) {
						end[k] = i;
					}
				}
				break;
			} else {
				count = count + 1;
			}
		}
		if (count == no)
			return -2;
	} /* end i */
	return 0;
}

void Sort_Leaves(char *ntk_names[], int n_l, int start[], int end[],
		int no_edges) {
	int i, j, k;
	char str1[20];
	for (i = 0; i < n_l; i++)
		for (j = i + 1; j < n_l; j++) {
			if (strcmp(ntk_names[i], ntk_names[j]) > 0) {
				strcpy(str1, ntk_names[i]);
				free(ntk_names[i]);
				k = strlen(ntk_names[j]);
				ntk_names[i] = (char *) malloc(k + 1);
				strcpy(ntk_names[i], ntk_names[j]);
				free(ntk_names[j]);
				k = strlen(str1);
				ntk_names[j] = (char *) malloc(k + 1);
				strcpy(ntk_names[j], str1);

				for (k = 0; k < no_edges; k++) {
					if (start[k] == i) {
						start[k] = -1;
					}
					if (start[k] == j) {
						start[k] = -2;
					}
					if (end[k] == i) {
						end[k] = -1;
					}
					if (end[k] == j) {
						end[k] = -2;
					}
				}

				for (k = 0; k < no_edges; k++) {
					if (start[k] == -1) {
						start[k] = j;
					}
					if (start[k] == -2) {
						start[k] = i;
					}
					if (end[k] == -1) {
						end[k] = j;
					}
					if (end[k] == -2) {
						end[k] = i;
					}
				}
			}
		}
}

void Child_Parent_Inform(struct lnode *child_array[],
		struct lnode *parent_array[], int no_nodes, int start[], int end[],
		int no_edges) {
	int i, j, x, y;

	for (i = 0; i < no_nodes; i++) {
		child_array[i] = NULL;
		parent_array[i] = NULL;
	}

	for (j = 0; j < no_edges; j++) {
		x = start[j];
		y = end[j];

		child_array[x] = ListExtend(child_array[x], y);
		parent_array[y] = ListExtend(parent_array[y], x);
	}
}

/* the negative return value indicates the input network graph is
 * not a phylogenetic network. The positive value is the number of
 * reticulation nodes in the network
 */
int Node_Type_Inform(int node_type[], int r_nodes[], int no_nodes, int start[],
		int end[], int no_edges, int *root) {
	int i, j, in, out, n_r;
	int check, check_node;

	check = 0;
	check_node = 0;
	n_r = 0;
	for (i = 0; i < no_nodes; i++) {
		in = 0;
		out = 0;
		for (j = 0; j < no_edges; j++) {
			if (end[j] == i)
				in = in + 1;
			if (start[j] == i)
				out = out + 1;
		}
		if (in == 0 && out > 1) {
			check = 1 + check;
			*root = i;
			node_type[i] = ROOT;
		}
		if (in == 1 && out == 0) {
			node_type[i] = LEAVE;
		}
		if (in == 1 && out >= 1)
			node_type[i] = TREE;
		if (in > 1 && out == 1) {
			r_nodes[n_r] = i;
			node_type[i] = RET;
			n_r = n_r + 1;
		}
		if (in > 1 && out > 1) {
			check_node = check_node + 1;
		}
	}
	if (check > 1 || check_node > 0)
		return -2;
	else
		return n_r;
}

int Node_Type_Inform1(int node_type[], int no_nodes, int start[], int end[],
		int no_edges, int *root) {
	int i, j, in, out;
	int check, check_node;

	check = 0;
	check_node = 0;

	for (i = 0; i < no_nodes; i++) {
		in = 0;
		out = 0;
		for (j = 0; j < no_edges; j++) {
			if (end[j] == i)
				in = in + 1;
			if (start[j] == i)
				out = out + 1;
		}
		if (in == 0 && out > 1) {
			check = 1 + check;
			*root = i;
			node_type[i] = ROOT;
		}
		if (in == 1 && out == 0) {
			node_type[i] = LEAVE;
		}
		if (in == 1 && out >= 1)
			node_type[i] = TREE;
		if (in > 1 && out == 1) {
			node_type[i] = RET;
		}
		if (in > 1 && out > 1) {
			check_node = check_node + 1;
		}
	}
	if (check > 1 || check_node > 0)
		return -2;
	else
		return 0;
}

/* The component is stable if it contains a leaf or a reticulation node below it is 'INNER' */
int Is_Stable(struct arb_tnode *comp_ptr, int node_type[], int inner_flag[],
		int lf_below[]) {
	int i, deg;

	if (comp_ptr == NULL)
		return -1;
	else {
		if (node_type[comp_ptr->label] == LEAVE)
			return 1;
		else if (node_type[comp_ptr->label] == RET) {
			if (inner_flag[comp_ptr->label] == INNER
					&& lf_below[comp_ptr->label] >= 0)
				return 1;
			else
				return 0;
		} else if (node_type[comp_ptr->label] == TREE
				|| node_type[comp_ptr->label] == ROOT) {
			deg = comp_ptr->no_children;
			for (i = 0; i < deg; i++) {
				if (Is_Stable((comp_ptr->child)[i], node_type, inner_flag,
						lf_below) == 1)
					return 1;
			}
			return 0;
		}
	}
}

/* lf_below_comp: the leaves below the component (to simply the component) */
void Find_UnStable(struct arb_tnode *comp_ptr, int input_leaves[], int no_leaf,
		int unstb_rets_in[], int *no_rets_in, int unstb_rets_out[],
		int *no_rets_out, int node_type[], int inner_flag[], int lf_below[], int lf_in_comp[], int *no_in_lfb, int lf_out_comp[], int *no_out_lfb) {
	int i, deg;

	if (comp_ptr == NULL)
		return;
	else {
		if (node_type[comp_ptr->label] == LEAVE){ // should not occur, since the component is invisible
			return;
		}
		else if (node_type[comp_ptr->label] == RET) {
			if (inner_flag[comp_ptr->label] == CROSS) {
				int leaf = lf_below[comp_ptr->label];
				if (leaf == -2) return;
				if (Is_In(leaf, input_leaves, no_leaf) == 1) {
					unstb_rets_in[*no_rets_in] = comp_ptr->label;
					*no_rets_in = *no_rets_in + 1;
					lf_in_comp[*no_in_lfb] = leaf;
					*no_in_lfb = *no_in_lfb + 1;
				} else {
					unstb_rets_out[*no_rets_out] = comp_ptr->label;
					*no_rets_out = *no_rets_out + 1;
					lf_out_comp[*no_out_lfb] = leaf;
					*no_out_lfb = *no_out_lfb + 1;
				}
			}
		} else if (node_type[comp_ptr->label] == TREE
				|| node_type[comp_ptr->label] == ROOT) {
			deg = comp_ptr->no_children;
			for (i = 0; i < deg; i++) {
				Find_UnStable((comp_ptr->child)[i], input_leaves, no_leaf,
						unstb_rets_in, no_rets_in, unstb_rets_out, no_rets_out,
						node_type, inner_flag, lf_below, lf_in_comp, no_in_lfb, lf_out_comp, no_out_lfb);
			}
		}
		return;
	}
}


int Make_ArbTree_Copy(struct arb_tnode *src_tree, struct arb_tnode *dest_tree,
		struct arb_tnode trees[], int *tree_index) {
	int i, deg, res;
	//printf("weird \n");
	if (src_tree == NULL)
		return 0;

	//printf("not null \n");
	dest_tree->label = src_tree->label;
	dest_tree->flag = src_tree->flag;
	deg = src_tree->no_children;
	dest_tree->no_children = deg;
	//printf("deg %d\n", deg);
	for (i = 0; i < deg; i++) {
		struct arb_tnode *child = &trees[(*tree_index)];
		*tree_index += 1;
		res = Make_ArbTree_Copy((src_tree->child)[i], child, trees,
				tree_index);
		if (res == 0) {
			(dest_tree->child)[i] = NULL;
		} else {
			(dest_tree->child)[i] = child;
		}
		//printf("\ntree_index %d\n", *tree_index);

	}
	return 1;
}

void *Make_Current_Network(struct components *p, int no_comp,
		struct components network[], struct arb_tnode trees[], int *tree_index) {
	struct components *ptr;
	int i, res;

	if (p == NULL)
		return NULL;
	ptr = p;
	i = 0;
	while (ptr != NULL) {
		//printf("i %d\n", i);
		network[i].ret_node = ptr->ret_node;
		network[i].inner = ptr->inner;
		network[i].size = ptr->size;
		network[i].no_tree_node = ptr->no_tree_node;
		//printf("copy trees\n");
		if (ptr->size == 0){
			network[i].tree_com = NULL;
		}
		else{
			network[i].tree_com = &trees[(*tree_index)];
			*tree_index += 1;
			//printf("tree_com label\n",network[i].tree_com->label);
			res = Make_ArbTree_Copy(ptr->tree_com, network[i].tree_com, trees,
					tree_index);
			if (res == 0) {
				network[i].tree_com = NULL;
			}
		}
		if (i < no_comp - 1) {
			network[i].next = &network[i + 1];
		} else {
			network[i].next = NULL;
		}
		//printf("when copying, ret node %d\n", ptr->ret_node);
		ptr = ptr->next;
		i += 1;
	}
}


void Destroy_Arbtree(struct arb_tnode *tree) {
	int i, deg;

	if (tree != NULL) {
		deg = tree->no_children;
		for (i = 0; i < deg; i++)
			Destroy_Arbtree((tree->child)[i]);
		free(tree);
	}
}

void Destroy_Network(struct components *cmp) {
	if (cmp != NULL) {
		if (cmp->next != NULL) {
			Destroy_Network(cmp->next);
		}
		Destroy_Arbtree(cmp->tree_com);
		free(cmp);
	}
}

void Free_Lnodes(struct lnode* head) {
	struct lnode* tmp;

	while (head != NULL) {
		tmp = head;
		head = head->next;
		free(tmp);
	}
}

void Modify1(struct arb_tnode *p, int node_type[], int unstb_ret,
		int *comp_size, int no_nodes, int *net_edges) {
	struct arb_tnode *ptr;
	int i, k, j, deg;
	struct arb_tnode *tmp;

	if (p == NULL)
		return;

	if (node_type[p->label] == LEAVE) {
		return;
	} else if (node_type[p->label] == RET) {
		return;
	} else if (node_type[p->label] == TREE || node_type[p->label] == ROOT) {
		deg = p->no_children;
		for (i = 0; i < deg; i++) {
			ptr = (p->child)[i];
			if (ptr->label == unstb_ret) {
//				tmp = (p->child)[i];
//				Destroy_Arbtree(tmp);
				// printf("delete edge %d\t%d\n", p->label, ptr->label);
				// net_edges[p->label][ptr->label]=0;
				*(net_edges + p->label*no_nodes + ptr->label) = 0;
				(p->child)[i] = NULL;
				*comp_size = *comp_size - 1;
			} else {
				Modify1((p->child)[i], node_type, unstb_ret, comp_size, no_nodes, net_edges);
			}
		}

		k = deg;
		for (i = 0; i < deg; i++) {
			if ((p->child)[i] == NULL)
				k = k - 1;
		}

		p->no_children = k;

		for (i = 0; i < deg; i++) {
			if ((p->child)[i] == NULL) {
				j = i + 1;
				while ((p->child)[j] == NULL && j < deg)
					j = j + 1;
				(p->child)[i] = (p->child)[j];
				(p->child)[j] = NULL;
			}
		}
	}
}

void Modify2(struct components *p, int node_type[], int x, int no_nodes, int *net_edges) {
	struct components *p_copy;

	if (p != NULL) {
		p_copy = p;
		while (p_copy != NULL) {
			if (p_copy->tree_com != NULL)
				Modify1(p_copy->tree_com, node_type, x, &p_copy->size, no_nodes, net_edges);
			p_copy = p_copy->next;
		}
	}
}

/*
 *	For network pointed by p, remove all parents of unstb_ret in other components. (The size of these other components reduce by 1)
 * For network pointed by p1, exclude current component from new network. (The size of current component reduce by 1)
 */
void Modify(struct components *p, struct components *p1, int node_type[],
		int unstb_ret, int no_nodes, int *net_edges, int *net_edges1) {
	struct components *ptr;
	//struct arb_tnode *tmp;

	if (p == NULL)
		return;

	ptr = p->next;
	while (ptr != NULL) {
		if (ptr->tree_com != NULL) {
			if ((ptr->tree_com)->label == unstb_ret) {
				//tmp = ptr->tree_com;
				//Destroy_Arbtree(tmp);
				// printf("delete edge %d\t%d\n", ptr->ret_node, unstb_ret);
				// net_edges[ptr->ret_node][unstb_ret]=0;
				*(net_edges + ptr->ret_node * no_nodes + unstb_ret) = 0;
				ptr->tree_com = NULL;
				ptr->size = ptr->size - 1;
			} else {
				// search the ret node recursively in the tree comp
				Modify1(ptr->tree_com, node_type, unstb_ret, &ptr->size, no_nodes, net_edges);
			}
		}
		ptr = ptr->next;
	}

	if (p1 == NULL || p1->tree_com == NULL)
		return;
	if ((p1->tree_com)->label == unstb_ret) {
		//tmp = p1->tree_com;
		//Destroy_Arbtree(tmp);
		// printf("delete edge1 %d\t%d\n", p1->ret_node, unstb_ret);
		// net_edges1[p1->ret_node][unstb_ret]=0;
		*(net_edges1 + p1->ret_node * no_nodes + unstb_ret) = 0;
		p1->tree_com = NULL;
		p1->size = p1->size - 1;
	} else {
		Modify1(p1->tree_com, node_type, unstb_ret, &p1->size, no_nodes, net_edges1);
	}
}


void Print_tree11(struct arb_tnode *tree, int node_type[],
		struct lnode *child_array[], char *node_strings[]) {
	int deg, i;
	struct lnode *tmp;

	if (tree != NULL) {
		deg = tree->no_children;
		for (i = 0; i < deg; i++) {
			printf("%s %s\n", node_strings[tree->label],
					node_strings[(tree->child[i])->label]);
			Print_tree11(tree->child[i], node_type, child_array, node_strings);
		}
		if (deg == 0 && node_type[tree->label] == RET
				&& child_array[tree->label] != NULL) {
			printf("%s %s\n", node_strings[tree->label],
					node_strings[child_array[tree->label]->leaf]);
			tmp = child_array[tree->label];
			free(tmp);
			child_array[tree->label] = NULL;
		}
	} else
		return;
}

/* all the ret nodes have been replaced by leaves */
void Rebuilt_Component(struct arb_tnode *tree, int *rpl_comp, int node_type[],
		char *node_strings[]) {
	int i, x, y;

	if (tree == NULL)
		return;
	if (tree != NULL) {
		if (tree->no_children == 0) {
			x = tree->label;
			if (node_type[x] == LEAVE) {
				/* the leaf is used to replace ret node */
				// if (rpl_comp[x] != -1) {
				if (rpl_comp[x] >= 0) {
					/* y is the child of tree->label, parent of x */
					y = rpl_comp[x];
					tree->label = y;
				}
			}
			return;
			/* non leaf */
		} else {
			for (i = 0; i < tree->no_children; i++) {
				Rebuilt_Component((tree->child)[i], rpl_comp, node_type,
						node_strings);
			}
			return;
		}
	} /* end non trivial case */
}

void Modify_Cross_Ret(int n_r, int lf_below[], int r_nodes[], int no_opt,
		int node_type[], int* optional, char* node_strings[], int* in_cluster,
		struct components* p, int no_nodes, int *net_edges) {
	int i, x;
	/* remove edges entering CR(C) */
	for (i = 0; i < n_r; i++) {
		x = lf_below[r_nodes[i]];
		if (x >= 0) {
			if (Is_In(x, optional, no_opt) == 1) {
				if (in_cluster[x] == 1) {
					Modify2(p->next, node_type, r_nodes[i], no_nodes, net_edges);
					lf_below[r_nodes[i]] = -2;
				} else if (in_cluster[x] == 0) {
					Modify1(p->tree_com, node_type, r_nodes[i], &p->size, no_nodes, net_edges);
				}
			}
		}
	}
}

void Modify_Cross_Ret1(int n_r, int lf_below[], int r_nodes[], int no_opt,
		int node_type[], int* optional, char* node_strings[], int* in_cluster,
		struct components* p, int no_nodes, int *net_edges) {
	int i, x;
	for (i = 0; i < n_r; i++) {
		x = lf_below[r_nodes[i]];
		if (x >= 0 && Is_In(x, optional, no_opt) == 1) {
			if (in_cluster[x] == 0) {
				Modify2(p->next, node_type, r_nodes[i], no_nodes, net_edges);
				lf_below[r_nodes[i]] = -2;
			} else if (in_cluster[x] == 1) {
				Modify1(p->tree_com, node_type, r_nodes[i], &p->size, no_nodes, net_edges);
			}
		}
	}
}


int Count_Parent(int child, struct lnode *parent_array[], int no_nodes, int *net_edges) {
	int count = 0;
	struct lnode* parent = parent_array[child];
	while(parent!=NULL){
		// printf("parent %s\n", node_strings[parent->leaf]);
		// if(net_edges[parent->leaf][child]==0){
		if(*(net_edges + parent->leaf * no_nodes + child) == 0){
			parent = parent->next;
			continue;	// The edge has been deleted
		}
		count +=1;
		parent = parent->next;
	}
	return count;
}



// Check whether it is feasible for the subtree below a node to display the input cluster
// indicator -- to show whether the leaf should be in the input or not. For 1st network, indicator=1. For 2nd network, indicator=-1.
int Is_Feasible_Node(int parent, int curr_leaf, int indicator, int no_nodes, int no1, int input_leaves[], int node_type[], int inner_flag[], int lf_below[], char *node_strings[], struct lnode *child_array[],
	struct lnode *parent_array[], int *net_edges)
{
	int i;
	int num_parent;
	int no_children = Count_Child(child_array[parent]);
	struct lnode* child = child_array[parent];
	for (i = 0; i < no_children; i++) {
		int a_leaf = child->leaf;
		// printf("child %s\n", node_strings[a_leaf]);
		if (a_leaf==curr_leaf){child = child->next; continue;}
		// if (net_edges[parent][a_leaf]==0 ){child = child->next; continue;}
		if(*(net_edges + parent * no_nodes + a_leaf) == 0){child = child->next; continue;}

		if (node_type[a_leaf]==RET)
		{
			int l_below = lf_below[a_leaf];
			if (l_below!=-2 && l_below==curr_leaf) {child = child->next; continue;}
			num_parent = Count_Parent(a_leaf, parent_array, no_nodes, net_edges);
			if(num_parent>=2 && l_below==-2) return 1;	// reticulate node that has not been processed
			if(num_parent<=1 && Is_In(l_below, input_leaves, no1) == indicator) return 0;
		}
		else if (node_type[a_leaf]==LEAVE)
		{
			if (Is_In(a_leaf, input_leaves, no1) == indicator){
				return 0;
			}
		}
		else{ // TREE node, traverse until leaves
			return Is_Feasible_Node(a_leaf, curr_leaf, indicator, no_nodes, no1, input_leaves, node_type, inner_flag, lf_below, node_strings, child_array,
				parent_array, net_edges);
		}
		// printf("Go to next child\n");
		child = child->next;
	}
	return 1;
}


// Check whether to continue running on one network
int To_Run_Network(int unstb_ret, int indicator, int no_nodes, int no1, int input_leaves[], int node_type[], int inner_flag[], int lf_below[], char *node_strings[], struct lnode *child_array[],
	struct lnode *parent_array[], int *net_edges){
	int to_run=1;
	int curr_leaf = lf_below[unstb_ret];
	struct lnode* parent = parent_array[unstb_ret];
	while(parent!=NULL && to_run == 1){
		// printf("parent %s\n", node_strings[parent->leaf]);
		// if(net_edges[parent->leaf][unstb_ret]==0){
		if(*(net_edges + parent->leaf * no_nodes + unstb_ret) == 0){
			parent = parent->next;
			continue;	// The edge has been deleted
		}

		to_run = Is_Feasible_Node(parent->leaf, curr_leaf, indicator, no_nodes, no1, input_leaves, node_type, inner_flag, lf_below, node_strings, child_array,
			parent_array, net_edges);
		if (to_run==0)	break;

		parent = parent->next;
	}
	return to_run;
}


int Cluster_Containment(struct components *ptr, int r_nodes[], int n_r,
		int no_nodes, int node_type[], int inner_flag[], int lf_below[],
		char *node_strings[], int no1, int *input_leaves, int* in_cluster,
		int super_deg[], struct components *cps, struct lnode *child_array[], struct lnode *parent_array[], int *net_edges,
		int n_l, int *no_break) {
	int i, j;
	int no, no_slf, no_ambig, no_opt;

	int nlf_kept; /* no. of leaves to keep in B */
	int no_vmax, no_mark;

	struct components *p, *p_copy;
	struct components *p1, *whole_copy;
	int unstb_ret;
	int no1_1;	// copy of no1
	int res, is_cluster, num_inleaf, count_in, count_out;

	p = ptr;
	if (p == NULL)
		return 0;

	if (p->tree_com == NULL) {
		Modify2(p->next, node_type, p->ret_node, no_nodes, net_edges);
		return Cluster_Containment(p->next, r_nodes, n_r, no_nodes, node_type,
				inner_flag, lf_below, node_strings, no1, input_leaves,
				in_cluster, super_deg, cps, child_array, parent_array, net_edges, n_l, no_break);
	}
	else if (Is_Stable(p->tree_com, node_type, inner_flag, lf_below) == 1) {
		struct arb_tnode* postList[2 * no_nodes];
		no = 0;
		PostTrans_Revised(p->tree_com, postList, &no);

		no_slf = 0;
		no_ambig = 0;
		no_opt = 0;
		int sleaves[n_l], ambig[n_l], optional[n_l], rpl_comp[n_l];
		for (i = 0; i < n_l; i++) {
			rpl_comp[i] = -1;
		}

		/* build a tree from the component */
		Replace_Ret_Revised(p->tree_com, inner_flag, node_type, lf_below,
				sleaves, &no_slf, ambig, &no_ambig, optional, &no_opt,
				node_strings, rpl_comp, super_deg);

		for (i = 0; i < n_r; i++) {
			if (inner_flag[r_nodes[i]] == REVISED) {
				if (super_deg[r_nodes[i]] > 2) {
					super_deg[r_nodes[i]] = super_deg[r_nodes[i]] - 1;
					inner_flag[r_nodes[i]] = CROSS;
				} else {
					super_deg[r_nodes[i]] = 1;
					inner_flag[r_nodes[i]] = INNER;
				}
			}
		}

		if (no_slf > 0) {
			if(no_opt == 0 && no_slf == 1 ){	// There are only one stable leaf below the component
				if (no1 == 1 && sleaves[0] == input_leaves[0]){
					return 50;
				}
				else{	// There are more than one input leaves
					lf_below[p->ret_node] = sleaves[0];
					return Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
							node_type, inner_flag, lf_below, node_strings, no1,
							input_leaves, in_cluster, super_deg, cps, child_array, parent_array, net_edges, n_l,
							no_break);
				}
			}
			else	// There are more than one stable leaves below the component
			{
				/* mark nodes and find Vmax */
				Initiallize(p->tree_com);
				no_mark = 0;
				no_vmax = 0;
				/* mark ambiguous leaves */
				for (i = 0; i < no_ambig; i++) {
					if (in_cluster[ambig[i]] == 0) {
						Mark_Revised(p->tree_com, ambig[i], &no_mark);
					}
				}
				/* mark a leaf that is neither ambiguous nor optional */
				for (i = 0; i < no_slf; i++) {
					if (Check_List(ambig, no_ambig, sleaves[i]) == -1
							&& in_cluster[sleaves[i]] == 0) {
						Mark_Revised(p->tree_com, sleaves[i], &no_mark);
					}
				}

				int vmax[no];
				if (no_mark == 0) {
					vmax[0] = p->tree_com->label;
					no_vmax = 1;
				} else {
					Find_Vmax(p->tree_com, vmax, &no_vmax);
				}

				int map_nodes[no_vmax][MAXSIZE];
				is_cluster = DProgram_Revised(node_strings, p->tree_com, no1,
						map_nodes, vmax, no_vmax, input_leaves, node_type);
				Rebuilt_Component(p->tree_com, rpl_comp, node_type, node_strings);
			}

			if (is_cluster >= 0) {
				/* remove edges entering CR(C) for visualization */
				Modify_Cross_Ret(n_r, lf_below, r_nodes, no_opt, node_type,
						optional, node_strings, in_cluster, p, no_nodes, net_edges);
				return 50;
			} else {
				/* use one stable leaf to replace the current component */
				if (node_type[p->ret_node] != ROOT){
					for (i = 0; i < n_r; i++) {
						if (lf_below[r_nodes[i]] == sleaves[0]){
							lf_below[r_nodes[i]] = -2;
						}
					}
					lf_below[p->ret_node] = sleaves[0];
				}

				count_out = 0;
				count_in = 0;
				for (i = 0; i < no_slf; i++) {
					if (in_cluster[sleaves[i]] == 0) {
						count_out += 1;
					} else if (in_cluster[sleaves[i]] == 1) {
						count_in += 1;
					}
				}

				/* L and B are disjoint */
				if (count_out == no_slf) {
					Modify_Cross_Ret1(n_r, lf_below, r_nodes, no_opt, node_type,
							optional, node_strings, in_cluster, p, no_nodes, net_edges);
					return Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
							node_type, inner_flag, lf_below, node_strings, no1,
							input_leaves, in_cluster, super_deg, cps,
							child_array, parent_array, net_edges, n_l, no_break);
				}
				/* L and notB are disjoint */
				else if (count_in == no_slf) {
					/* check whether B^==B */
					num_inleaf = 0;
					for (i = 0; i < no_slf; i++) {
						if (in_cluster[sleaves[i]] == 1)
							num_inleaf += 1;
					}
					for (i = 0; i < no_opt; i++) {
						if (in_cluster[optional[i]] == 1)
							num_inleaf += 1;
					}

					if (num_inleaf == no1) {
						/* remove edges related to CR(C) */
						Modify_Cross_Ret(n_r, lf_below, r_nodes, no_opt,
								node_type, optional, node_strings, in_cluster,
								p, no_nodes, net_edges);
						return 50;
					}
					/* remove edges related to CR(C) */
					Modify_Cross_Ret(n_r, lf_below, r_nodes, no_opt, node_type,
							optional, node_strings, in_cluster, p, no_nodes, net_edges);

					/* decrease B */
					if (no_slf + no_opt > 1){
						int input_leaves1[no1];
						nlf_kept = 0;
						for (i = 0; i < no1; i++) {
							if (Is_In(input_leaves[i], sleaves, no_slf) == -1
									&& Is_In(input_leaves[i], optional, no_opt)
											== -1) {
								input_leaves1[nlf_kept++] = input_leaves[i];
							}
						}
						input_leaves1[nlf_kept++] = sleaves[0];
						no1 = nlf_kept;

						/* revise in_cluster */
						int in_cluster1[n_l];
						for (i = 0; i < n_l; i++) {
							in_cluster1[i] = in_cluster[i];
							if (Is_In(i, input_leaves1, no1) == -1) {
								in_cluster1[i] = 0;
							}
						}
						res = Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
								node_type, inner_flag, lf_below, node_strings, no1,
								input_leaves1, in_cluster1, super_deg, cps,
								child_array, parent_array, net_edges, n_l, no_break);
					}
					else{
						res = Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
								node_type, inner_flag, lf_below, node_strings, no1,
								input_leaves, in_cluster, super_deg, cps,
								child_array, parent_array, net_edges, n_l, no_break);
					}

					return res;
				}
				/* L intersects with both B and notB */
				else {
					return 10;
				}
			}
			if (p->next == NULL) {
				return 0;
			}
		} else {
			//  Empty Component
			Rebuilt_Component(p->tree_com, rpl_comp, node_type, node_strings);
			unstb_ret = p->tree_com->label;
			Modify(p->next, NULL, node_type, unstb_ret, no_nodes, net_edges, NULL);
			return Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
					node_type, inner_flag, lf_below, node_strings, no1,
					input_leaves, in_cluster, super_deg, cps, child_array, parent_array, net_edges, n_l,
					no_break);
		}
	}
	else {
		// Unstable case
		int no_rets_in = 0;
		int no_rets_out = 0;
		int no_in_lfb = 0;
		int no_out_lfb = 0;

		int unstb_rets_in[n_r];
		int unstb_rets_out[n_r];
		int lf_in_comp[no1];
		int lf_out_comp[no1];

		Find_UnStable(p->tree_com, input_leaves, no1, unstb_rets_in,
				&no_rets_in, unstb_rets_out, &no_rets_out, node_type,
				inner_flag, lf_below, lf_in_comp, &no_in_lfb, lf_out_comp, &no_out_lfb);

		// check whether leaves below current component equals to B
		if(no_in_lfb == no1){
			return 50;
		}

		if (no_rets_in > 0 || no_rets_out > 0){
		// split into two networks at first
			struct components network[n_r + 1];
			int tree_size = 0;
			p1 = cps;
			while (p1 != NULL) {
				tree_size += p1->size;
				p1 = p1->next;
			}
			struct arb_tnode trees[tree_size];
			int tree_index = 0;
			Make_Current_Network((cps), n_r + 1, network, trees, &tree_index);
			whole_copy = &network[0];

			p1 = whole_copy;
			while (p1->ret_node != p->ret_node)
				p1 = p1->next;

			int lf_below1[no_nodes];
			int inner_flag1[no_nodes];
			int super_deg1[no_nodes];
			// int net_edges1[no_nodes][no_nodes];
			int net_edges1[no_nodes * no_nodes];

			// Coying network
			for (i = 0; i < no_nodes; i++) {
				inner_flag1[i] = inner_flag[i];
				lf_below1[i] = lf_below[i];
				super_deg1[i] = super_deg[i];
				for(j = 0; j < no_nodes; j++){
					// net_edges1[i][j]=net_edges[i][j];
					*(net_edges1 + i * no_nodes + j) = *(net_edges + i * no_nodes + j);
				}
			}

			// Begin modifying network
			for (i = 0; i < no_rets_in; i++) {
				unstb_ret = unstb_rets_in[i];
				if (inner_flag[unstb_ret] == CROSS) {
					inner_flag[unstb_ret] = INNER;
					inner_flag1[unstb_ret] = REVISED;
					super_deg1[unstb_ret] = super_deg[unstb_ret] - 1; /* exclude current component from new network*/
					super_deg[unstb_ret] = 1; /* remove all parents in other comps. */
					if (super_deg1[unstb_ret] == 1){
						inner_flag1[unstb_ret] = INNER;
					}
					else{
						inner_flag1[unstb_ret] = CROSS;
					}
				}
				Modify(p, p1, node_type, unstb_ret, no_nodes, net_edges, net_edges1);
			}

			for (i = 0; i < no_rets_out; i++) {
				unstb_ret = unstb_rets_out[i];
				if (inner_flag[unstb_ret] == CROSS) {
					inner_flag[unstb_ret] = REVISED;
					inner_flag1[unstb_ret] = INNER;
					super_deg[unstb_ret] = super_deg[unstb_ret] - 1;
					super_deg1[unstb_ret] = 1; /* remove all parents in other comps. */
					if (super_deg[unstb_ret] == 1) {
						inner_flag[unstb_ret] = INNER;
					}
					else{
						inner_flag[unstb_ret] = CROSS;
					}
				}
				Modify(p1, p, node_type, unstb_ret, no_nodes, net_edges1, net_edges);
			}

			/* copy data for spliting */
			int input_leaves_orig[no1];
			int in_cluster_orig[n_l];
			for (i = 0; i < n_l; i++) {
				in_cluster_orig[i] = in_cluster[i];
			}
			for (i = 0; i < no1; i++) {
				input_leaves_orig[i] = input_leaves[i];
			}
			no1_1 = no1;

			*no_break = *no_break + 1;

			// All leaves below the current component are not in B
			if(no_in_lfb == 0){
				lf_below[p->ret_node] = -2;
			}
			else //if(no_in_lfb > 0)
			{
				/* replace the current component by a single leaf */
				for (i = 0; i < n_r; i++) {
					if (lf_below[r_nodes[i]] == lf_in_comp[0]){
						lf_below[r_nodes[i]] = -2;
					}
				}
				lf_below[p->ret_node] = lf_in_comp[0];
				// Exclude cross-reticulation nodes whose visible leaves are in the input
				for (i = 0; i < no_rets_in; i++) {
					lf_below[unstb_rets_in[i]] = -2;
				}
			}

			if(no_out_lfb == 0){
				lf_below1[p1->ret_node] = -2;
			}
			else // if(no_out_lfb > 0)
			{
				/* replace the current component by a single leaf */
				for (i = 0; i < n_r; i++) {
					if (lf_below1[r_nodes[i]] == lf_out_comp[0]){
						lf_below1[r_nodes[i]] = -2;
					}
				}
				lf_below1[p1->ret_node] = lf_out_comp[0];
				// Exclude cross-reticulation nodes whose visible leaves are not in the input
				for (i = 0; i < no_rets_out; i++) {
					lf_below1[unstb_rets_out[i]] = -2;
				}
			}

			// Check network 2 to see if it is good to continue or not
			int run_1st = 1;
			int run_2nd = 1;
			int indicator = 1;
			// not run the 1st network if there is a node which has children in both B and not B
			for (i = 0; i < no_rets_out; i++) {
				unstb_ret = unstb_rets_out[i];
				run_1st = To_Run_Network(unstb_ret, indicator, no_nodes, no1, input_leaves, node_type, inner_flag, lf_below, node_strings, child_array,
				parent_array, net_edges);
				if(run_1st==0) break;
			}
			// not run the 2nd network if there is a node which has children in both B and not B
			indicator = -1;
			for (i = 0; i < no_rets_in; i++) {
				unstb_ret = unstb_rets_in[i];
				run_2nd = To_Run_Network(unstb_ret, indicator, no_nodes, no1_1, input_leaves_orig, node_type, inner_flag1, lf_below1, node_strings, child_array,
				parent_array, net_edges1);
				if (run_2nd==0) break;
			}

			res = 0;
			if (run_1st == 0 && run_2nd == 0)
			{
				return 10;	// not a cluster in either network
			}
			if (run_1st == 1)
			{
				if(no_in_lfb > 1){
					/* decrease B */
					int input_leaves1[no1];
					nlf_kept = 0;
					for (i = 0; i < no1; i++) {
						if (Is_In(input_leaves[i], lf_in_comp, no_in_lfb) == -1) {
							input_leaves1[nlf_kept++] = input_leaves[i];
						}
					}
					input_leaves1[nlf_kept++] = lf_in_comp[0];
					no1 = nlf_kept;

					/* revise in_cluster */
					int in_cluster1[n_l];
					for (i = 0; i < n_l; i++) {
						in_cluster1[i] = in_cluster[i];
						if (Is_In(i, input_leaves1, no1) == -1) {
							in_cluster1[i] = 0;
						}
					}
					res = Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
							node_type, inner_flag, lf_below, node_strings, no1,
							input_leaves1, in_cluster1, super_deg, cps,
							child_array, parent_array, net_edges, n_l, no_break);
				}
				else{
					res = Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
							node_type, inner_flag, lf_below, node_strings, no1,
							input_leaves, in_cluster, super_deg, cps,
							child_array, parent_array, net_edges, n_l, no_break);
				}
			}
			if (res != 50  && run_2nd == 1) {
				// Run on 2nd split network
				res = Cluster_Containment(p1->next, r_nodes, n_r, no_nodes, node_type,
					inner_flag1, lf_below1, node_strings, no1_1,
					input_leaves_orig, in_cluster_orig, super_deg1,
					whole_copy, child_array, parent_array, net_edges1, n_l, no_break);
			}
			// free(net_edges1);
			return res;
		}
		else {
			Modify2(p->next, node_type, p->ret_node, no_nodes, net_edges);
			return Cluster_Containment(p->next, r_nodes, n_r, no_nodes,
					node_type, inner_flag, lf_below, node_strings, no1,
					input_leaves, in_cluster, super_deg, cps, child_array, parent_array, net_edges, n_l,
					no_break);
		}
	}
}



void Print_Network(struct network *net) {
	int i;
	struct components *p;

	printf("Network nodes\n   ");
	for (i = 0; i < net->no_nodes; i++) {
		printf("%s(%d) ", net->node_strings[i], i);
		if ((i + 1) % 5 == 0)
			printf("\n   ");
	}

// print out reticulation nodes in post-order
//	printf("\nRet nodes in post-order:\n");
//	for (i = 0; i < net->n_r; i++)
//		printf("%s ", net->node_strings[net->r_nodes[i]]);
//	printf("\n");
//

//	p = (net->all_cps);
//	while (p != NULL) {
//		printf("---ret node %d\n", p->ret_node);
//		printf("size %d \n", p->size);
//		Print_Comp_Revised(p->tree_com, net->node_strings);
//		printf("---\n");
//		p = p->next;
//	}
}

/*
 * check whether a subset of leaves is a cluster of a network
 */
int Is_Cluster(int in_cluster[], int r, struct network *net1,
		struct network *net2, int tree_size1, int tree_size2) {
	int size = max((*net1).no_nodes, (*net2).no_nodes);
	int inner_flag[size], lf_below[size], super_deg[size];
	struct components *cps1, *cps2, *p1, *p2;
	int no_break, r1 = 0, r2 = 0, res = 0;
	int i, j;
	if (r == 0 || r == net1->n_l) {
		return;
	}
	if (r == 1) {
	} else {
		int input_leaves[r];
		j = 0;
		for (i = 0; i < net1->n_l; i++) {
			if (in_cluster[i] == 1) {
				input_leaves[j] = i;
				j += 1;
			}
		}
		//printf("\ncheck whether this cluster is in the 1st network\n   ");
		no_break = 0;
		// Coying network
		int net_edges1[(*net1).no_nodes * (*net1).no_nodes];
		for (i = 0; i < (*net1).no_nodes; i++) {
			inner_flag[i] = net1->inner_flag[i];
			lf_below[i] = net1->lf_below[i];
			super_deg[i] = net1->super_deg[i];
			for(j = 0; j < (*net1).no_nodes; j++){
				*(net_edges1 + i * (*net1).no_nodes + j) = *(net1->net_edges + i * (*net1).no_nodes + j);
			}
		}
		struct components network1[net1->n_r + 1];
		struct arb_tnode trees1[tree_size1];
		int tree_index1 = 0;
		Make_Current_Network((net1->all_cps), net1->n_r + 1, network1, trees1,
				&tree_index1);
		cps1 = &network1[0];
		p1 = cps1;
		if (net1->n_r > 0) {
			while (net1->node_type[p1->ret_node] != ROOT
					&& net1->node_type[(net1->child_array[p1->ret_node])->leaf]
							== LEAVE) {
				p1 = p1->next;
			}
		}

		r1 = Cluster_Containment(p1, net1->r_nodes, net1->n_r, net1->no_nodes,
				net1->node_type, inner_flag, lf_below, net1->node_strings, r,
				input_leaves, in_cluster, super_deg, cps1, net1->child_array, net1->parent_array, net_edges1,
				net1->n_l, &no_break);

		//printf("\ncheck whether this cluster is in the 2nd network\n   ");
		no_break = 0;
		int net_edges2[(*net2).no_nodes * (*net2).no_nodes];
		for (i = 0; i < (*net2).no_nodes; i++) {
			inner_flag[i] = net2->inner_flag[i];
			lf_below[i] = net2->lf_below[i];
			super_deg[i] = net2->super_deg[i];
			for(j = 0; j < (*net2).no_nodes; j++){
				*(net_edges2 + i * (*net2).no_nodes + j) = *(net2->net_edges + i * (*net2).no_nodes + j);
			}
		}
		struct components network2[net2->n_r + 1];
		struct arb_tnode trees2[tree_size2];
		int tree_index2 = 0;
		Make_Current_Network((net2->all_cps), net2->n_r + 1, network2, trees2,
				&tree_index2);
		cps2 = &network2[0];
		p2 = cps2;
		if (net2->n_r > 0) {
			while (net2->node_type[p2->ret_node] != ROOT
					&& net2->node_type[(net2->child_array[p2->ret_node])->leaf]
							== LEAVE) {
				p2 = p2->next;
			}
		}

		r2 = Cluster_Containment(p2, net2->r_nodes, net2->n_r, net2->no_nodes,
				net2->node_type, inner_flag, lf_below, net2->node_strings, r,
				input_leaves, in_cluster, super_deg, cps2, net2->child_array, net2->parent_array, net_edges2,
				net2->n_l, &no_break);

		if ((r1 == 50 && r2 < 50) || (r2 == 50 && r1 < 50)) {
			res = 1;
		}
	}

	return res;
}

/*
 * Read the input network
 * Build the tree component
 */
void Preprocess_Network(char *arg, struct network *net) {
	FILE *ntk_ptr;
	int *node_type, *r_nodes, *orig_rnodes;
	int root;
	int start[MAXEDGE], end[MAXEDGE];
	char *node_strings[MAXSIZE];
	struct lnode **child_array;
	struct lnode **parent_array;
	int *lf_below; /* what is the leaf below a reticulation */
	int *inner_flag; /* whether a ret is inner or cross */
	int *super_deg;
	char **net_leaves; /* to denote leaves and move leaves front */
	int *in_cluster; /*  to indicate whether a network leaf is in the input cluster B or not*/
	int no_edges, n_t, n_r, n_l, no_nodes; /* n_t: tree nodes, n_r: ret nodes; n_l: no. leaves */
	int *net_edges;	// Use adjacency matrix to store all edges to facilitate edge looking up

	int check_leaves;
	char str1[20], str2[20];
	int u1, u2;
	int i, x, j;

	struct components *all_cps, *p;

	/* network processing */
	ntk_ptr = fopen(arg, "r");
	if (ntk_ptr == NULL)
		printf("File %s is not readable\n", arg);
	no_edges = 0;
	no_nodes = 0;
	while (fscanf(ntk_ptr, "%s %s\n", str1, str2) != EOF) {
		u1 = Check_Name(node_strings, no_nodes, str1);
		if (u1 == -1) {
			u1 = no_nodes, no_nodes = 1 + no_nodes;
			node_strings[u1] = (char *) malloc(strlen(str1) + 1);
			strcpy(node_strings[u1], str1);
		}
		u2 = Check_Name(node_strings, no_nodes, str2);
		if (u2 == -1) {
			u2 = no_nodes, no_nodes = 1 + no_nodes;
			node_strings[u2] = (char *) malloc(strlen(str2) + 1);
			strcpy(node_strings[u2], str2);
		}
		start[no_edges] = u1;
		end[no_edges] = u2;
		no_edges += 1;
	}
	fclose(ntk_ptr);

	/*	printf("no_nodes: %d\n", no_nodes);
	 printf("no_edges: %d\n", no_edges);*/

	node_type = (int *) calloc(no_nodes, sizeof(int));

	/* no_edges, no_nodes  */
	x = Node_Type_Inform1(node_type, no_nodes, start, end, no_edges, &root);
	if (x < 0) {
		printf("\n the network graph has two or more roots or a node with");
		printf("\n both in- and out-degree greater than 1;\n Recheck it\n");
		return;
	}

	n_l = 0;
	n_r = 0;
	for (i = 0; i < no_nodes; i++) {
		if (node_type[i] == LEAVE) {
			n_l = n_l + 1;
		} else if (node_type[i] == RET) {
			n_r = n_r + 1;
		}
	}
	/*	printf("n_l: %d\n", n_l);
	 printf("n_r: %d\n", n_r);*/

	net_leaves = (char **) calloc(n_l, sizeof(char*));
	j = 0;
	for (i = 0; i < no_nodes; i++) {
		if (node_type[i] == LEAVE) {
			net_leaves[j] = (char *) malloc(strlen(node_strings[i]) + 1);
			strcpy(net_leaves[j], node_strings[i]);
			j += 1;
		}
	}

	//printf("move leaves to front.\n");
	Move_Leaves_Front(node_strings, no_nodes, start, end, no_edges, net_leaves,
			n_l);
	//printf("sort leaves.\n");
	Sort_Leaves(node_strings, n_l, start, end, no_edges);
	//printf("inform node type.\n");
	Node_Type_Inform1(node_type, no_nodes, start, end, no_edges, &root);

	net_edges = malloc(no_nodes * no_nodes * sizeof(int));
	for  (i=0; i < no_nodes; i++)
		for  (j=0; j < no_nodes; j++)
			*(net_edges + i*no_nodes + j) = 0;

	for (i=0; i<no_edges; i++){
		// net_edges[start[i]][end[i]]=1;
		*(net_edges + start[i]*no_nodes + end[i]) = 1;
	}

	orig_rnodes = (int *) calloc(n_r, sizeof(int));
	r_nodes = (int *) calloc(n_r, sizeof(int));
	j = 0;
	for (i = 0; i < no_nodes; i++) {
		if (node_type[i] == RET) {
			orig_rnodes[j] = i;
			r_nodes[j] = i;
			j+=1;
		}
	}

	child_array = (struct lnode **) calloc(no_nodes, sizeof(struct lnode*));
	parent_array = (struct lnode **) calloc(no_nodes, sizeof(struct lnode*));
	//printf("inform parent-child relationship.\n");
	Child_Parent_Inform(child_array, parent_array, no_nodes, start, end,
			no_edges);
	//printf("sort ret nodes.\n");
	Sort_Rets_By_Level(orig_rnodes, r_nodes, n_r, child_array, parent_array, node_type, no_nodes);

	inner_flag = (int *) calloc(no_nodes, sizeof(int));
	for (i = 0; i < no_nodes; i++)
		inner_flag[i] = -2;

	//printf("add components.\n");
	all_cps = (struct components *) malloc(sizeof(struct components));
	if (n_r > 0) {
		(*all_cps).ret_node = r_nodes[0];
		x = Is_Inner_Revised(r_nodes[0], parent_array, node_type, no_nodes);
		inner_flag[r_nodes[0]] = x;
		(*all_cps).inner = x;
		(*all_cps).size = 1;
		(*all_cps).tree_com = (struct arb_tnode *) malloc(sizeof(struct arb_tnode));
		((*all_cps).tree_com)->label = child_array[r_nodes[0]]->leaf;
		if(node_type[child_array[r_nodes[0]]->leaf]==RET){
			(*all_cps).no_tree_node = 0;
		}else{
			(*all_cps).no_tree_node = 1;
		}
		((*all_cps).tree_com)->flag = 0;
		((*all_cps).tree_com)->no_children = 0;
		for (i = i; i < MAXDEGREE; i++)
			(((*all_cps).tree_com)->child)[i] = NULL;
		(*all_cps).next = NULL;

		/* identify which reticulation is inner */
		for (i = 1; i < n_r; i++) {
			x = Is_Inner_Revised(r_nodes[i], parent_array, node_type, no_nodes);
			inner_flag[r_nodes[i]] = x;
			Add_Component(all_cps, r_nodes[i], child_array[r_nodes[i]]->leaf, x, node_type);
		}

		/* treat root as CROSS node, why??? */
		Add_Component(all_cps, root, root, CROSS, node_type);
	} else {
		(*all_cps).ret_node = root;
		inner_flag[root] = CROSS;
		(*all_cps).inner = CROSS;
		(*all_cps).size = 1;
		(*all_cps).no_tree_node = 1;
		(*all_cps).tree_com = (struct arb_tnode *) malloc(sizeof(struct arb_tnode));
		((*all_cps).tree_com)->label = root;
		((*all_cps).tree_com)->flag = 0;
		((*all_cps).tree_com)->no_children = 0;
		for (i = i; i < MAXDEGREE; i++)
			(((*all_cps).tree_com)->child)[i] = NULL;
		(*all_cps).next = NULL;
	}

	super_deg = (int *) calloc(no_nodes, sizeof(int));
	for (i = 0; i < n_r; i++)
		super_deg[r_nodes[i]] = 0;

	//printf("build components.\n");
	p = all_cps;
	while (p != NULL) {
		Build_Comp_Revised(p->tree_com, child_array, node_type, no_nodes, &p->size,
				&p->no_tree_node);
		for (i = 0; i < n_r; i++) {
			super_deg[r_nodes[i]] = super_deg[r_nodes[i]]
					+ Is_In_Comp(p->tree_com, r_nodes[i]);
		}

		// Print_Comp_Revised(p->tree_com, node_strings);
		// printf("---size %d--no_tree_node %d\n", p->size, p->no_tree_node);

		p = p->next;
	}

	lf_below = (int *) calloc(no_nodes, sizeof(int));
	for (i = 0; i < n_r; i++)
		lf_below[r_nodes[i]] = -2;

	p = all_cps;
	if (n_r > 0) {
		while (node_type[p->ret_node] != ROOT
				&& node_type[(child_array[p->ret_node])->leaf] == LEAVE) {
			lf_below[p->ret_node] = (child_array[p->ret_node])->leaf;
			p = p->next;
		}
	}

	//printf("assign variables.\n");
	net->inner_flag = inner_flag;
	net->all_cps = all_cps;
	net->parent_array = parent_array;
	net->child_array = child_array;
	net->lf_below = lf_below;
	net->n_l = n_l;
	net->n_r = n_r;
	net->no_nodes = no_nodes;
	net->node_strings = (char **) calloc(no_nodes, sizeof(char*));
	for (i = 0; i < no_nodes; i++) {
		net->node_strings[i] = (char *) malloc(strlen(node_strings[i]) + 1);
		strcpy(net->node_strings[i], node_strings[i]);
		free(node_strings[i]);
	}
	net->node_type = node_type;
	net->r_nodes = r_nodes;
	net->root = root;
	net->super_deg = super_deg;
	net->net_edges = net_edges;

	for (i = 0; i < n_l; i++) {
		free(net_leaves[i]);
	}
	free(net_leaves);
}

void Free_Network(struct network *net) {
	int i;
	struct components* p;

	/*	Free memory at the end */
	for (i = 0; i < net->no_nodes; i++) {
		free(net->node_strings[i]);
	}
	free(net->node_strings);
	free(net->node_type);
	free(net->r_nodes);
	free(net->inner_flag);
	free(net->lf_below);
	free(net->super_deg);

	for (i = 0; i < net->no_nodes; i++) {
		Free_Lnodes(net->child_array[i]);
		Free_Lnodes(net->parent_array[i]);
		// free(net->net_edges[i]);
	}
	free(net->child_array);
	free(net->parent_array);
	free(net->net_edges);

	Destroy_Network(net->all_cps);
}


void print_array(int n, int array[]) {
	int i;
	for (i = 0; i < n; i++) {
		printf("%d ", array[i]);
	}
	printf("\n");
}

double Find_Cluster_Distance(char *arg1, char *arg2) {
	int i;
	struct network net1, net2;
	unsigned long no_res;
	float dist;
	unsigned long k;
	int tree_size1 = 0, tree_size2 = 0;
	struct components *p1;
	/* network processing */
//printf("preprocess 1st network: \n");
	Preprocess_Network(arg1, &net1);
//printf("preprocess 2nd network: \n");
	Preprocess_Network(arg2, &net2);

	printf("1st network: \n");
	Print_Network(&net1);
	printf("\n2nd network: \n");
	Print_Network(&net2);

	/* make sure the two networks have the same set of leaves */
	if (net1.n_l != net2.n_l) {
		printf(
				"\n The networks have different number of leaves;\nRecheck it\n");
		return;
	} else {
		for (i = 0; i < net1.n_l; i++) {
			if (strcmp(net1.node_strings[i], net2.node_strings[i]) != 0) {
				printf("\n The networks have different leaves;\nRecheck it\n");
				return;
			}
		}
	}

	p1 = net1.all_cps;
	while (p1 != NULL) {
		tree_size1 += p1->size;
		p1 = p1->next;
	}

	p1 = net2.all_cps;
	while (p1 != NULL) {
		tree_size2 += p1->size;
		p1 = p1->next;
	}

	int n = net1.n_l;
	no_res = (1U << n);

	int num_thread = omp_get_num_procs();
	printf("\nThe number of threads: %d\n", num_thread);
	omp_set_num_threads(num_thread);
	int chunksize = no_res / num_thread;
	printf("The size of chunk: %d\n", chunksize);

	int no_diff = 0;

#pragma omp parallel for schedule(static,chunksize) reduction (+:no_diff)
	for (k = 1; k < no_res - 1; k++) {
		printf("");
		int in_cluster[n];
		int_to_bin_digit(k, n, in_cluster);
		int r = pop(k);
		//print_array(n, in_cluster);
		//printf("r %d\n",r);
		no_diff += Is_Cluster(in_cluster, r, &net1, &net2, tree_size1,
				tree_size2);
	}

	dist = (float) (no_diff) / 2;

	/*	Free memory at the end */
	Free_Network(&net1);
	Free_Network(&net2);

	return dist;
}

void main(int argc, char *argv[]) {
	if (argc != 3) {
		printf("Command: PROGRAM(./psrfd) network_file1_name network_file2_name\n");
		return;
	}
	if (strcmp(argv[1], argv[2]) == 0) {
		printf(
				"\nThe two network files are the same.\nThe soft Robinson-Foulds distance between the two input networks is: %.1f\n",
				0.0);
		return;
	}

	float dist;
	dist = Find_Cluster_Distance(argv[1], argv[2]);

	printf(
			"\nThe soft Robinson-Foulds distance between the two input networks is: %.1f\n",
			dist);

	return;
}
