package client.ui;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

/**
 * "Utility" class that handles reading input from system input,
 * and makes it convenient for calling side to acquire specific data.
 */
public class SysUtility {
    /**
     * Holds the input stream of the instance.
     */
    private final BufferedReader input = new BufferedReader(new InputStreamReader(System.in));

    /**
     * Method that attempts to read user input string from system in.
     *
     * @param promptText String text that will be displayed that prompts user for input
     * @return String retrieved value, or null if an error occurred
     */
    public String readString(String promptText) {
        // User prompt
        System.out.println(promptText);

        try {
            return this.input.readLine();
        } catch (IOException e) {
            return null;
        }
    }

    /**
     * Method that attempts to read user input integer from system in.
     *
     * @param promptText String text that will be displayed that prompts user for input
     * @return int retrieved value, or -1 if an error occurred
     */
    public int readInteger(String promptText) {
        try {
            return Integer.parseInt(this.readString(promptText));
        } catch (NumberFormatException e) {
            return -1;
        }
    }

}
