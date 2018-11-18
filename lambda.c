#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>

char* read_file(char* path) {
    FILE* file = fopen(path, "rb");
    if (!file) {
        fprintf(stderr, "Failed to open file: %s\n", path);
        return NULL;
    }

    fseek(file, 0, SEEK_END);
    long len = ftell(file);
    char* content = malloc(len);
    fseek(file, 0, SEEK_SET);
    size_t read = 0;
    while (
        !feof(file)
        && !ferror(file)
        && len > (read = fread(&content[0], sizeof(char), len, file))
    );
    if (feof(file) || ferror(file)) {
        fprintf(stderr, "Failed to read entire file: %s\n", path);
        return NULL;
    }

    return content;
}

// Lexemes: (, ), \, A-9, .,  , ,, <, >
typedef enum LexemeId_t {
    NIL,
    LEFT, // (
    RIGHT, // )
    LAMBDA, // \_
    VAR, // A-9
    DEFINE, //.
    APPLY, //
    DELIM, // ,
    COMMENT_LEFT, // <
    COMMENT_RIGHT // >
} LexemeId;
typedef struct Lexeme_t {
    LexemeId id;
    size_t literal_len;
    char* literal;
} Lexeme;

typedef struct DynLexeme {
    size_t n;
    size_t alloc;
    Lexeme* lexemes; 
} DynLexeme;
void init_DynLexeme(DynLexeme* d, size_t size) {
    d->n = 0;
    d->alloc = size;
    d->lexemes = malloc(size * sizeof(Lexeme));
}
void free_DynLexeme(DynLexeme* d) {
    for (int i = 0; i < d->n; ++i) {
        free(d->lexemes[i].literal);
    }
    free(d->lexemes);
    d->lexemes = NULL;
    d->alloc = 0;
    d->n = 0;
}
void DynLexeme_push(DynLexeme* d, Lexeme l) {
    if (d->n == d->alloc) {
        d->alloc *= 2;
        d->lexemes = realloc(d->lexemes, d->alloc * sizeof(Lexeme));
    }
    Lexeme* end = &(d->lexemes[d->n]);

    // copy l into end
    end->id = l.id;
    end->literal_len = l.literal_len;
    end->literal = malloc(end->literal_len * sizeof(char));
    for (int i = 0; i < end->literal_len; ++i) {
        end->literal[i] = l.literal[i];
    }

    ++d->n; 
}
Lexeme DynLexeme_pop(DynLexeme* d) {
    Lexeme l;
    if (d->n == 0) {
        l.id = NIL;
        l.literal_len = 0;
        l.literal = NULL;
        return l;
    }

    Lexeme end = d->lexemes[d->n - 1];

    // copy end into l
    l.id = end.id;
    l.literal_len = end.literal_len;
    l.literal = malloc(l.literal_len * sizeof(char));
    for (int i = 0; i < l.literal_len; ++i) {
        l.literal[i] = end.literal[i];
    }

    free(end.literal);
    end.literal = NULL;
    --d->n;
    return l;
}
Lexeme DynLexeme_peek(DynLexeme *d) {
    if (d->n == 0) {
        Lexeme l;
        l.literal = NULL;
        return l;
    } else {
        return d->lexemes[d->n - 1];
    }
}
void DynLexeme_reverse(DynLexeme* src, DynLexeme* target) {
    // TODO: make more efficient (use heap less!)
    while (src->n > 0) {
        Lexeme l = DynLexeme_pop(src);
        DynLexeme_push(target, l);
        free(l.literal);
        l.literal = NULL;
    }
}

bool is_alnum(char c) {
    return ('0' <= c && c <= '9')
        || ('A' <= c && c <= 'Z')
        || ('a' <= c && c <= 'z');
}

//terms:
//      variable: x
//      abstraction: (\x.T)
//      application: (T1 T2)
//      ordering: (T)
//comments:
//      <...>
DynLexeme lex(char* program) {
    DynLexeme lexemes;
    init_DynLexeme(&lexemes, 64);
    
    for (int i = 0; program[i];) {
        Lexeme l;
        l.literal_len = 0;
        DynLexeme_push(&lexemes, l);
        Lexeme* cur = &(lexemes.lexemes[lexemes.n - 1]);
        char x = program[i];
        switch(x) {
        case '(': //LEFT
            cur->id = LEFT;
            cur->literal_len = 1;
            break;
        case ')': //RIGHT
            cur->id = RIGHT;
            cur->literal_len = 1;
            break;
        case '\\': //LAMBDA
            cur->id = LAMBDA;
            cur->literal_len = 1;
            break;
        case '.': //DEFINE
            cur->id = DEFINE;
            cur->literal_len = 1;
            break;
        case ' ': //APPLY
            cur->id = APPLY;
            cur->literal_len = 1;
            break;
        case ',': //DELIM
            cur->id = DELIM;
            cur->literal_len = 1;
            break;
        case '<': //COMMENT_LEFT
            cur->id = COMMENT_LEFT;
            cur->literal_len = 1;
            int depth = 1;
            while (!(program[i + cur->literal_len] == '>' && depth == 1)) {
                if (program[i + cur->literal_len] == '<') {
                    ++depth;
                } else if (program[i + cur->literal_len] == '>') {
                    --depth;
                }
                ++cur->literal_len;
            }
            break;
        case '>': //COMMENT_RIGHT
            cur->id = COMMENT_RIGHT;
            cur->literal_len = 1;
            break;
        default: //VAR
            if (is_alnum(x)) {
                cur->id = VAR;
                cur->literal_len = 1;
                while (is_alnum(program[i + cur->literal_len])) {
                    ++cur->literal_len;
                }; 
            }
        }
        cur->literal = realloc(cur->literal, cur->literal_len * sizeof(char));
        for (int j = 0; j < cur->literal_len; ++j) {
            cur->literal[j] = program[i + j];
        }
        i += (cur->literal_len < 1 ? 1 : cur->literal_len);
    } 

    return lexemes;
}
           
DynLexeme simplify(DynLexeme* lexemes) {
    DynLexeme simple;
    init_DynLexeme(&simple, lexemes->n);
    for (int i = 0; i < lexemes->n;) {
        Lexeme l = DynLexeme_pop(lexemes);
        if (l.id == COMMENT_LEFT || l.id == COMMENT_RIGHT) {
            free(l.literal);
            l.literal = NULL;
            continue;
        }
        if (l.id == DELIM) {
            free(l.literal);
            l.literal = NULL;

            Lexeme lambda;
            lambda.id = LAMBDA;
            lambda.literal_len = 1;
            lambda.literal = malloc(lambda.literal_len * sizeof(char));
            lambda.literal[0] = '\\';
            DynLexeme_push(&simple, lambda);

            Lexeme define;
            define.id = DEFINE;
            define.literal_len = 1;
            define.literal = malloc(define.literal_len * sizeof(char));
            define.literal[0] = '.';
            DynLexeme_push(&simple, define);
            continue;
        }

        DynLexeme_push(&simple, l);
    }
    return simple;
}

typedef enum Terminal_t {
    T_NIL,
    T_EXP,
    T_VAR,
    T_ABS,
    T_APP
} Terminal;
struct AST_t;
typedef struct Var_t {
    size_t len;
    char* id;
} Var;
typedef struct Abs_t {
    Var par;
    struct AST_t* def;
} Abs;
typedef struct App_t {
    struct AST_t* fun;
    struct AST_t* arg;
} App;
typedef struct AST_t {
    Terminal t;
    union {
        Var v;
        Abs f;
        App c;
    };
} AST;

void init_AST(AST* a) {
    a->t = T_NIL;
}

void free_AST(AST* a) {
    switch(a->t) {
    case T_VAR:
        free(a->v.id);
        a->v.id = NULL;
        break;
    case T_ABS:
        free(a->f.par.id);
        a->f.par.id = NULL;
        free_AST(a->f.def);
        a->f.def = NULL;
        break;
    case T_APP:
        free_AST(a->c.fun);
        a->c.fun = NULL;
        free_AST(a->c.arg);
        a->c.arg = NULL;
        break;
    case T_EXP:
    case T_NIL:
    default:
        break;
    } 
    free(a);
    a = NULL;
}

Var Variable(Lexeme l) {
    assert(l.id == VAR);
    Var v;
    v.len = l.literal_len;
    v.id = malloc(v.len * sizeof(char));
    for (int i = 0; i < v.len; ++i) {
        v.id[i] = l.literal[i];
    }
    free(l.literal);
    l.literal = NULL;
    return v;
}
AST ASTVar(Var v) { return (AST){.t = T_VAR, .v = v}; }

Abs Abstract(Var v, AST* d) {
    Abs a;
    a.par = v;
    a.def = d;
    return a;
}
AST ASTAbs(Abs a) { return (AST){.t = T_ABS, .f = a}; }

App Apply(AST* f, AST* r) {
    App a;
    a.fun = f;
    a.arg = r;
    return a;
}
AST ASTApp(App a) { return (AST){.t = T_APP, .c = a}; }

bool expect_Lexeme(DynLexeme* lexemes, LexemeId t) {
    Lexeme l = DynLexeme_pop(lexemes);
    free(l.literal);
    l.literal = NULL;
    return l.id != t;
}

bool expect_VAR(Var* v, DynLexeme* lexemes) {
    Lexeme l = DynLexeme_pop(lexemes);
    if (l.id == VAR) {
        *v = Variable(l);
        return 0;
    } else {
        free(l.literal);
        l.literal = NULL;
        return 1;
    }
}

bool expect_EXPR(AST** a, DynLexeme* lexemes);
bool expect_ARG(AST** a, DynLexeme* lexemes);

bool maybe_APPLY(AST** prior, DynLexeme* lexemes) {
    Lexeme l = DynLexeme_pop(lexemes);
    if (l.id == APPLY) {
        AST* a = malloc(sizeof(AST));
        init_AST(a);
        if (expect_ARG(&a, lexemes)) {
            free(l.literal);
            l.literal = NULL;
            return 1;
        }
        AST* newPrior = malloc(sizeof(AST));
        init_AST(newPrior);
        *newPrior = ASTApp(Apply(*prior, a));
        *prior = newPrior;
        free(l.literal);
        l.literal = NULL;
        return maybe_APPLY(prior, lexemes);
    } else if (l.id == RIGHT) {
        DynLexeme_push(lexemes, l);
        return 0;
    } else if (l.id == NIL) {
        free(l.literal);
        l.literal = NULL;
        return 0;
    } else {
        free(l.literal);
        l.literal = NULL;
        return 1;
    }
}

bool expect_ARG(AST** a, DynLexeme* lexemes) {
    Lexeme l = DynLexeme_pop(lexemes);
    if (l.id == VAR) {
        **a = ASTVar(Variable(l));
    } else if (l.id == LEFT) {
        expect_EXPR(a, lexemes);
        if (expect_Lexeme(lexemes, RIGHT)) {
            free(l.literal);
            l.literal = NULL;
            return 1;
        }
    } else if (l.id == LAMBDA) {
        Var v;
        if (expect_VAR(&v, lexemes)) {
            free(l.literal);
            l.literal = NULL;
            return 1;
        }
        if (expect_Lexeme(lexemes, DEFINE)) {
            free(l.literal);
            l.literal = NULL;
            return 1;
        }
        AST* d = malloc(sizeof(AST));
        init_AST(d);
        if (expect_EXPR(&d, lexemes)) {
            free(l.literal);
            l.literal = NULL;
            return 1;
        }
        **a = ASTAbs(Abstract(v, d));
    } else {
        free(l.literal);
        l.literal = NULL;
        return 1;
    }
    return 0;
}


bool expect_EXPR(AST** a, DynLexeme* lexemes) {
    if (expect_ARG(a, lexemes)) {
        return 1;
    } else {
        return maybe_APPLY(a, lexemes);
    }
}

void AST_fprint(FILE* f, AST* a) {
    switch (a->t) {
    case T_NIL:
        fprintf(f, "NIL");
        break;
    case T_EXP:
        fprintf(f, "EXPR");
        break;
    case T_VAR:
        fprintf(f, "VAR(");
        for (int i = 0; i < a->v.len; ++i) {
            fprintf(f, "%c", a->v.id[i]);
        }
        fprintf(f, ")");
        break;
    case T_ABS:
        fprintf(f, "LAMBDA(");
        for (int i = 0; i < a->f.par.len; ++i) {
            fprintf(f, "%c", a->f.par.id[i]);
        }
        fprintf(f, ",");
        AST_fprint(f, a->f.def);
        fprintf(f, ")");
        break;
    case T_APP:
        fprintf(f, "APPLY(");
        AST_fprint(f, a->c.fun);
        fprintf(f, ",");
        AST_fprint(f, a->c.arg);
        fprintf(f, ")");
        break;
    default:
        fprintf(f, "?");
        break;
    }
}
 
// _VAR
// _LEFT ...
// _LEFT ... _RIGHT
// _LAMBDA ...
// _LAMBDA _VAR ...
// _LAMBDA _VAR _DEFINE ...        
// ...
// ... _APPLY
// ... _APPLY ...
//outermost parentheses are dropped
//left associative applications M N P == ((M N) P)
//abstraction extends as far right as possible \x.M N == \x.(M N)
//abstracions are contracted \x.\y.\z.N == \x,y,z.N (or \xyz.N)

AST* parse(DynLexeme lexemes) {
    // \x.x
    // LAMBDA(VAR(X), VAR(X))
    // \x.x y
    // LAMBDA(VARX), APPLY(VAR(X), VAR(Y)))
    AST* a = malloc(sizeof(AST));
    init_AST(a);
    if (expect_EXPR(&a, &lexemes) || lexemes.n) {
        fprintf(stderr, "Failed to parse.\n\tLast AST:\n");
        AST_fprint(stderr, a);
        fprintf(stderr, "\n");
        fprintf(stderr, "\tRemaining After Failure:\n");
        while(lexemes.n > 0) {
            Lexeme l = DynLexeme_pop(&lexemes);
            for (int i = 0; i < l.literal_len; ++i) {
                fprintf(stderr, "%c", l.literal[i]);
            }
            free(l.literal);
            l.literal = NULL;
        }
        fprintf(stderr, "\n");
        return NULL;
    }
    return a;
}

//rules:
//      a-conversion (\x.T[x]) -> (\y.T[y])
//      n-conversion \x.M x -> M only if x not in FV(M) 
//      b-reduction ((\x.T1) T2) -> (T1[x:=T2])
// \ binds interior things. unbound things are free.
// FV(x) = {x}; FV(\x.M) = FV(M)\{x}; FV(M N) = FV(M) u FV(N)
// if FV(M) = {}, then M is closed.
// 
// Normal Order Reduction: leftmost, outermost redex first.
//      arguments substituted before arguments are reduced
//      Call-by-need = name function application arguments that would duplicate
//              implemented as a pointer to a singular object that's reduced
//              once.

/*
char* evaluate(AST* a) {
    alpha_convert(a);
    fv = free_var(a)
    while (a=LAMBDA(VAR(_), EXPR) where x not in fv) { eta_convert(a) }
    while (a=APPLY(LAMBDA(VAR(_), EXPR), EXPR)) { beta_reduce(a, BY_NEED) }
    if (a = APPLY(EXPR`1, EXPR`2)) {
        evaluate(EXPR`1)
        evaluate(a)
        evaluate(EXPR`2)
    }

    return "";
}
*/

void interpret(char* program) {
    printf("== LEXER ==\n");
    DynLexeme lexemes = lex(program);
    DynLexeme simple = simplify(&lexemes);
    while (simple.n > 0) {
        Lexeme l = DynLexeme_pop(&simple);
        char* literal = calloc(l.literal_len + 1, sizeof(char));
        for (int i = 0; i < l.literal_len; ++i) {
            literal[i] = l.literal[i];
        }
        printf("%d %zu %s\n",
            l.id,
            l.literal_len,
            (literal[0] == '\\' ? "\u03BB" : literal)
        );
        DynLexeme_push(&lexemes, l);
        free(literal);
        free(l.literal);
        l.literal = NULL;
    }
    DynLexeme_reverse(&lexemes, &simple);
    free_DynLexeme(&lexemes);

    printf("== PARSER ==\n");
    AST* ast = parse(simple);
    if (!ast) {
        return;
    }
    AST_fprint(stdout, ast);
    printf("\n");

    //char* value = evaluate(ast, NORMAL_ORDER_BY_NEED);
    //printf("== EVAL ==\n%s\n", value);

    free_AST(ast);
}

void param(char* par, int* rem_argc, char*** rem_argv) {
}
void option(char* opt, int* rem_argc, char*** rem_argv) {
}
void flag(char* flags, int* rem_argc, char*** rem_argv) {
    for (int i = 0; flags[i]; ++i) {
        switch(flags[i]) {
        case 'i':
            //interpret
            if (*rem_argc > 1) {
               interpret((*rem_argv)[1]);
            }
            break;
        default:
            return;
        }
    }
}

int main(int argc, char**argv) {
    for (int i = 1; i < argc; ++i) {
        int rem_argc = argc-i;
        char** rem_argv = &(argv[i]);
        if (argv[i][0] == '-') {
            if (argv[i][1] == '-') {
                option(&(argv[i][2]), &rem_argc, &rem_argv);
            } else {
                flag(&(argv[i][1]), &rem_argc, &rem_argv);
            }
        } else {
            param(&(argv[i][0]), &rem_argc, &rem_argv);
        }
    }
}
