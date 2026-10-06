/*
 * json2dir: create the directory tree a JSON document describes, in the current directory.
 * Implements RFC J2D-1. ANSI C (C89) plus POSIX; hand-written UTF-8 check and JSON parser.
 */
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#define T_OBJ 1
#define T_STR 2
#define T_ARR 3

#define MAX_DEPTH 1000

struct node {
    int type;
    char *str;              /* T_STR: decoded bytes */
    size_t len;
    size_t n;               /* T_OBJ / T_ARR: number of children */
    size_t cap;
    struct node **kids;
    char **names;           /* T_OBJ: member names */
    size_t *namelens;
    size_t *order;          /* T_OBJ: original member index, for stable sorting */
};

static const unsigned char *in;
static size_t inlen;
static size_t pos;

static void fail(const char *msg)
{
    fprintf(stderr, "json2dir: %s\n", msg);
    exit(1);
}

static void fail2(const char *what, const char *path)
{
    fprintf(stderr, "json2dir: %s: %s\n", path, what);
    exit(1);
}

static void *xmalloc(size_t n)
{
    void *p = malloc(n ? n : 1);
    if (p == NULL)
        fail("out of memory");
    return p;
}

static void *xrealloc(void *p, size_t n)
{
    p = realloc(p, n ? n : 1);
    if (p == NULL)
        fail("out of memory");
    return p;
}

/* ---------- input ---------- */

static void read_stdin(void)
{
    size_t cap = 65536;
    ssize_t r;
    unsigned char *buf = (unsigned char *)xmalloc(cap);
    inlen = 0;
    for (;;) {
        if (inlen == cap) {
            cap *= 2;
            buf = (unsigned char *)xrealloc(buf, cap);
        }
        r = read(0, buf + inlen, cap - inlen);
        if (r < 0) {
            if (errno == EINTR)
                continue;
            fail("cannot read standard input");
        }
        if (r == 0)
            break;
        inlen += (size_t)r;
    }
    in = buf;
}

/* Strict UTF-8: no overlongs, no surrogates, nothing above U+10FFFF. */
static int utf8_valid(const unsigned char *s, size_t n)
{
    size_t i = 0, k, extra;
    unsigned long cp, min;
    while (i < n) {
        unsigned char c = s[i];
        if (c < 0x80) {
            i++;
            continue;
        } else if ((c & 0xE0) == 0xC0) {
            extra = 1; cp = c & 0x1F; min = 0x80;
        } else if ((c & 0xF0) == 0xE0) {
            extra = 2; cp = c & 0x0F; min = 0x800;
        } else if ((c & 0xF8) == 0xF0) {
            extra = 3; cp = c & 0x07; min = 0x10000;
        } else {
            return 0;
        }
        if (n - i <= extra)
            return 0;
        for (k = 1; k <= extra; k++) {
            if ((s[i + k] & 0xC0) != 0x80)
                return 0;
            cp = (cp << 6) | (unsigned long)(s[i + k] & 0x3F);
        }
        if (cp < min || cp > 0x10FFFFUL || (cp >= 0xD800UL && cp <= 0xDFFFUL))
            return 0;
        i += extra + 1;
    }
    return 1;
}

/* ---------- JSON parser ---------- */

static void skip_ws(void)
{
    while (pos < inlen && (in[pos] == ' ' || in[pos] == '\t' || in[pos] == '\n' || in[pos] == '\r'))
        pos++;
}

static struct node *new_node(int type)
{
    struct node *nd = (struct node *)xmalloc(sizeof *nd);
    memset(nd, 0, sizeof *nd);
    nd->type = type;
    return nd;
}

static int hexval(int c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static unsigned long read_hex4(void)
{
    unsigned long v = 0;
    int i, h;
    if (inlen - pos < 4)
        fail("invalid JSON: truncated \\u escape");
    for (i = 0; i < 4; i++) {
        h = hexval(in[pos + i]);
        if (h < 0)
            fail("invalid JSON: bad \\u escape");
        v = (v << 4) | (unsigned long)h;
    }
    pos += 4;
    return v;
}

static void put_utf8(char **buf, size_t *len, size_t *cap, unsigned long cp)
{
    if (*len + 4 > *cap) {
        *cap = *cap * 2 + 8;
        *buf = (char *)xrealloc(*buf, *cap);
    }
    if (cp < 0x80) {
        (*buf)[(*len)++] = (char)cp;
    } else if (cp < 0x800) {
        (*buf)[(*len)++] = (char)(0xC0 | (cp >> 6));
        (*buf)[(*len)++] = (char)(0x80 | (cp & 0x3F));
    } else if (cp < 0x10000UL) {
        (*buf)[(*len)++] = (char)(0xE0 | (cp >> 12));
        (*buf)[(*len)++] = (char)(0x80 | ((cp >> 6) & 0x3F));
        (*buf)[(*len)++] = (char)(0x80 | (cp & 0x3F));
    } else {
        (*buf)[(*len)++] = (char)(0xF0 | (cp >> 18));
        (*buf)[(*len)++] = (char)(0x80 | ((cp >> 12) & 0x3F));
        (*buf)[(*len)++] = (char)(0x80 | ((cp >> 6) & 0x3F));
        (*buf)[(*len)++] = (char)(0x80 | (cp & 0x3F));
    }
}

/* Parses a string starting at the opening quote. */
static char *parse_string(size_t *outlen)
{
    size_t cap = 16, len = 0;
    char *buf = (char *)xmalloc(cap);
    unsigned long cp, lo;
    unsigned char c;
    pos++;
    for (;;) {
        if (pos >= inlen)
            fail("invalid JSON: unterminated string");
        c = in[pos++];
        if (c == '"')
            break;
        if (c < 0x20)
            fail("invalid JSON: control character in string");
        if (c != '\\') {
            if (len + 1 > cap) {
                cap *= 2;
                buf = (char *)xrealloc(buf, cap);
            }
            buf[len++] = (char)c;
            continue;
        }
        if (pos >= inlen)
            fail("invalid JSON: unterminated string");
        c = in[pos++];
        switch (c) {
        case '"': cp = '"'; break;
        case '\\': cp = '\\'; break;
        case '/': cp = '/'; break;
        case 'b': cp = 8; break;
        case 'f': cp = 12; break;
        case 'n': cp = 10; break;
        case 'r': cp = 13; break;
        case 't': cp = 9; break;
        case 'u':
            cp = read_hex4();
            if (cp >= 0xDC00UL && cp <= 0xDFFFUL)
                fail("string contains an unpaired surrogate");
            if (cp >= 0xD800UL && cp <= 0xDBFFUL) {
                if (inlen - pos < 2 || in[pos] != '\\' || in[pos + 1] != 'u')
                    fail("string contains an unpaired surrogate");
                pos += 2;
                lo = read_hex4();
                if (lo < 0xDC00UL || lo > 0xDFFFUL)
                    fail("string contains an unpaired surrogate");
                cp = 0x10000UL + ((cp - 0xD800UL) << 10) + (lo - 0xDC00UL);
            }
            break;
        default:
            fail("invalid JSON: bad escape in string");
            cp = 0;
        }
        put_utf8(&buf, &len, &cap, cp);
    }
    *outlen = len;
    return buf;
}

static void add_kid(struct node *nd, struct node *kid, char *name, size_t namelen)
{
    if (nd->n == nd->cap) {
        nd->cap = nd->cap * 2 + 4;
        nd->kids = (struct node **)xrealloc(nd->kids, nd->cap * sizeof *nd->kids);
        nd->names = (char **)xrealloc(nd->names, nd->cap * sizeof *nd->names);
        nd->namelens = (size_t *)xrealloc(nd->namelens, nd->cap * sizeof *nd->namelens);
        nd->order = (size_t *)xrealloc(nd->order, nd->cap * sizeof *nd->order);
    }
    nd->kids[nd->n] = kid;
    nd->names[nd->n] = name;
    nd->namelens[nd->n] = namelen;
    nd->order[nd->n] = nd->n;
    nd->n++;
}

static struct node *parse_value(int depth)
{
    struct node *nd, *kid;
    char *name;
    size_t namelen;
    unsigned char c;

    if (depth > MAX_DEPTH)
        fail("document is nested too deeply");
    skip_ws();
    if (pos >= inlen)
        fail("invalid JSON: unexpected end of input");
    c = in[pos];
    if (c == '{') {
        nd = new_node(T_OBJ);
        pos++;
        skip_ws();
        if (pos < inlen && in[pos] == '}') {
            pos++;
            return nd;
        }
        for (;;) {
            skip_ws();
            if (pos >= inlen || in[pos] != '"')
                fail("invalid JSON: expected a member name");
            name = parse_string(&namelen);
            skip_ws();
            if (pos >= inlen || in[pos] != ':')
                fail("invalid JSON: expected ':'");
            pos++;
            kid = parse_value(depth + 1);
            add_kid(nd, kid, name, namelen);
            skip_ws();
            if (pos < inlen && in[pos] == ',') {
                pos++;
                continue;
            }
            if (pos < inlen && in[pos] == '}') {
                pos++;
                return nd;
            }
            fail("invalid JSON: expected ',' or '}'");
        }
    }
    if (c == '[') {
        nd = new_node(T_ARR);
        pos++;
        skip_ws();
        if (pos < inlen && in[pos] == ']') {
            pos++;
            return nd;
        }
        for (;;) {
            kid = parse_value(depth + 1);
            add_kid(nd, kid, NULL, 0);
            skip_ws();
            if (pos < inlen && in[pos] == ',') {
                pos++;
                continue;
            }
            if (pos < inlen && in[pos] == ']') {
                pos++;
                return nd;
            }
            fail("invalid JSON: expected ',' or ']'");
        }
    }
    if (c == '"') {
        nd = new_node(T_STR);
        nd->str = parse_string(&nd->len);
        return nd;
    }
    if (c == '-' || (c >= '0' && c <= '9'))
        fail("numbers are not allowed");
    if (c == 't' || c == 'f' || c == 'n')
        fail("true, false and null are not allowed");
    fail("invalid JSON: unexpected character");
    return NULL;
}

/* ---------- validation ---------- */

static int is_str(const struct node *nd, const char *s)
{
    size_t l = strlen(s);
    return nd->type == T_STR && nd->len == l && memcmp(nd->str, s, l) == 0;
}

static void validate(const struct node *nd)
{
    size_t i;
    if (nd->type == T_ARR) {
        if (nd->n != 2 || nd->kids[0]->type != T_STR || nd->kids[1]->type != T_STR)
            fail("an array must be [\"link\", target] or [\"script\", content]");
        if (!is_str(nd->kids[0], "link") && !is_str(nd->kids[0], "script"))
            fail("unknown array kind");
        if (is_str(nd->kids[0], "link") && memchr(nd->kids[1]->str, 0, nd->kids[1]->len) != NULL)
            fail("a link target cannot contain NUL");
        if (nd->kids[1]->len == 0 && is_str(nd->kids[0], "link"))
            fail("a link target cannot be empty");
        return;
    }
    if (nd->type != T_OBJ)
        return;
    for (i = 0; i < nd->n; i++) {
        const char *s = nd->names[i];
        size_t l = nd->namelens[i];
        if (l == 0 || (l == 1 && s[0] == '.') || (l == 2 && s[0] == '.' && s[1] == '.')
            || memchr(s, '/', l) != NULL || memchr(s, 0, l) != NULL)
            fail("invalid member name");
        validate(nd->kids[i]);
    }
}

/* ---------- applying ---------- */

static int cmp_names(const char *a, size_t al, const char *b, size_t bl)
{
    size_t m = al < bl ? al : bl;
    int r = memcmp(a, b, m);
    if (r != 0)
        return r;
    if (al != bl)
        return al < bl ? -1 : 1;
    return 0;
}

/* Insertion sort by name bytes, then by original position (so the last duplicate comes last). */
static void sort_members(struct node *nd)
{
    size_t i, j;
    for (i = 1; i < nd->n; i++) {
        struct node *k = nd->kids[i];
        char *nm = nd->names[i];
        size_t nl = nd->namelens[i];
        size_t od = nd->order[i];
        j = i;
        while (j > 0) {
            int r = cmp_names(nd->names[j - 1], nd->namelens[j - 1], nm, nl);
            if (r < 0 || (r == 0 && nd->order[j - 1] < od))
                break;
            nd->kids[j] = nd->kids[j - 1];
            nd->names[j] = nd->names[j - 1];
            nd->namelens[j] = nd->namelens[j - 1];
            nd->order[j] = nd->order[j - 1];
            j--;
        }
        nd->kids[j] = k;
        nd->names[j] = nm;
        nd->namelens[j] = nl;
        nd->order[j] = od;
    }
}

static void sys_fail(const char *path)
{
    fail2(strerror(errno), path);
}

/* Removes an existing non-directory; fails on a directory in the way. */
static void clear_entry(const char *path)
{
    struct stat st;
    if (lstat(path, &st) != 0) {
        if (errno == ENOENT)
            return;
        sys_fail(path);
    }
    if (S_ISDIR(st.st_mode))
        fail2("a directory is in the way", path);
    if (unlink(path) != 0)
        sys_fail(path);
}

static void write_file(const char *path, const char *data, size_t len, int executable)
{
    struct stat st;
    size_t done = 0;
    ssize_t w;
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0666);
    if (fd < 0)
        sys_fail(path);
    while (done < len) {
        w = write(fd, data + done, len - done);
        if (w < 0) {
            if (errno == EINTR)
                continue;
            sys_fail(path);
        }
        done += (size_t)w;
    }
    if (executable) {
        if (fstat(fd, &st) != 0 || fchmod(fd, (st.st_mode & 07777) | 0111) != 0)
            sys_fail(path);
    }
    if (close(fd) != 0)
        sys_fail(path);
}

static void apply(const char *dir, struct node *nd)
{
    size_t i, dl = strlen(dir);
    char *path;
    struct node *v;
    struct stat st;

    sort_members(nd);
    for (i = 0; i < nd->n; i++) {
        /* duplicate names: the last occurrence wins */
        if (i + 1 < nd->n && cmp_names(nd->names[i], nd->namelens[i], nd->names[i + 1], nd->namelens[i + 1]) == 0)
            continue;
        path = (char *)xmalloc(dl + 1 + nd->namelens[i] + 1);
        memcpy(path, dir, dl);
        path[dl] = '/';
        memcpy(path + dl + 1, nd->names[i], nd->namelens[i]);
        path[dl + 1 + nd->namelens[i]] = '\0';
        v = nd->kids[i];
        if (v->type == T_STR) {
            clear_entry(path);
            write_file(path, v->str, v->len, 0);
        } else if (v->type == T_ARR) {
            clear_entry(path);
            if (is_str(v->kids[0], "link")) {
                if (symlink(v->kids[1]->str, path) != 0)
                    sys_fail(path);
            } else {
                write_file(path, v->kids[1]->str, v->kids[1]->len, 1);
            }
        } else {
            if (lstat(path, &st) != 0) {
                if (errno != ENOENT)
                    sys_fail(path);
                if (mkdir(path, 0777) != 0)
                    sys_fail(path);
            } else if (!S_ISDIR(st.st_mode)) {
                if (unlink(path) != 0 || mkdir(path, 0777) != 0)
                    sys_fail(path);
            }
            apply(path, v);
        }
        free(path);
    }
}

/* Link targets need a terminating NUL for symlink(). */
static void terminate_strings(struct node *nd)
{
    size_t i;
    if (nd->type == T_STR) {
        nd->str = (char *)xrealloc(nd->str, nd->len + 1);
        nd->str[nd->len] = '\0';
        return;
    }
    for (i = 0; i < nd->n; i++)
        terminate_strings(nd->kids[i]);
}

int main(int argc, char **argv)
{
    struct node *root;
    (void)argv;
    if (argc > 1) {
        fprintf(stderr, "usage: json2dir < document.json\n");
        return 2;
    }
    read_stdin();
    if (!utf8_valid(in, inlen))
        fail("input is not valid UTF-8");
    pos = 0;
    if (inlen >= 3 && in[0] == 0xEF && in[1] == 0xBB && in[2] == 0xBF)
        pos = 3;
    skip_ws();
    if (pos >= inlen || in[pos] != '{')
        fail("the root of the document must be an object");
    root = parse_value(0);
    skip_ws();
    if (pos != inlen)
        fail("invalid JSON: trailing data after the document");
    validate(root);
    terminate_strings(root);
    apply(".", root);
    return 0;
}
