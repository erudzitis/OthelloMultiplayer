package game.ai;

/**
 * Factory generator class for ComputerPlayer
 */
public class ComputerPlayerFactory {
    private static final int PROFOUND = 2;

    /**
     * Generates ComputerPlayer instance based on the provided level. If level is invalid,
     * naive Strategy ComputerPlayer instance will be returned
     * @param level int, level of the AI. From 1 to 2
     * @return ComputerPlayer instance
     */
    public ComputerPlayer generateComputerPlayer(int level) {
        if (level == PROFOUND) {
            return new ComputerPlayer(new MiniMaxCornerStrategy());
        } else {
            return new ComputerPlayer(new NaiveStrategy());
        }
    }
}
