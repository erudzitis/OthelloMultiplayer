package helper;

import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

/**
 * Helper class that makes testing multithreaded asynchronous code more convenient
 * @param <T>
 */
public class Await<T extends Comparable> {
    /**
     * Constants that indicate delay time and times to re-try
     */
    private static final int DELAY_BETWEEN = 1000;
    private static final int MAX_TIMES_POSTPONE = 15;

    /**
     * Holds the state of the currently running methods result
     */
    private final CompletableFuture<T> state = new CompletableFuture<>();

    /**
     * Holds the amount of times the method was postponed
     */
    private int timesPostponed = 0;

    /**
     * Method that submits expression and waits for it to become equal to the expected result,
     * supports function chaining
     * @param method Method that yields certain result
     * @param expectedResult Expected result from the provided method
     * @return this
     */
    public Await<T> submitExpected(AwaitRunnable<T> method, T expectedResult) {
        T result = method.run();

        if (this.timesPostponed == MAX_TIMES_POSTPONE) {
            this.state.complete(null);
        }

        if ((result != null) && (result.compareTo(expectedResult) == 0)) {
            this.state.complete(result);
        } else {
            Executors.newSingleThreadScheduledExecutor().schedule(() -> this.submitExpected(method, expectedResult),
                    DELAY_BETWEEN, TimeUnit.MILLISECONDS);
            timesPostponed++;
        }

        return this;
    }

    /**
     * Method that delays the execution of a expression once for a given delay,
     * supports function chaining
     * @param method Method thats execution needs to be delayed
     * @return this
     */
    public Await<T> delay(AwaitRunnable<T> method) {
        Executors.newSingleThreadScheduledExecutor().schedule(() -> {
            state.complete(method.run());
        }, DELAY_BETWEEN, TimeUnit.MILLISECONDS);

        return this;
    }

    /**
     * Blocking call that waits for the delay or submitted method for execution to finish
     * @return T provided Type or null, if postpone limit exceeded
     * @throws ExecutionException
     * @throws InterruptedException
     */
    public T get() throws ExecutionException, InterruptedException {
        return this.state.get();
    }
}
