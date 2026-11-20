/* Report the peak resident set size of one checker process. */
#include <errno.h>
#include <stdio.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

int main(int argc, char **argv)
{
    struct rusage usage;
    pid_t child, ended;
    int status;
    unsigned long long bytes;

    if (argc < 2) {
        return 2;
    }
    child = fork();
    if (child < 0) {
        perror("fork");
        return 2;
    }
    if (child == 0) {
        execvp(argv[1], argv + 1);
        perror(argv[1]);
        _exit(127);
    }
    do {
        ended = waitpid(child, &status, 0);
    } while (ended < 0 && errno == EINTR);
    if (ended < 0 || getrusage(RUSAGE_CHILDREN, &usage) < 0) {
        perror("peak resident set size");
        return 2;
    }
    bytes = (unsigned long long)usage.ru_maxrss;
#if defined(__linux__)
    bytes *= 1024;
#endif
    fprintf(stderr, "peak-rss-bytes %llu\n", bytes);
    return WIFEXITED(status) ? WEXITSTATUS(status) : 2;
}
