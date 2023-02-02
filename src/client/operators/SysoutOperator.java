package client.operators;

import javax.sound.sampled.*;
import java.io.File;
import java.io.IOException;

/**
 * Consumes incoming messages for the client,
 * displays them in a TUI and plays corresponding sound effect.
 */
public class SysoutOperator implements MessageOperator {
    /**
     * Constants for text formatting and later on matched to a sound effect.
     */
    public static final String ERROR = "❌";
    public static final String INFO = "ℹ";
    public static final String UNKNOWN = "❓";
    public static final String PROMPT = "✍";
    public static final String SUCCESS = "\uD83D\uDCAF";
    public static final String LOCK = "\uD83D\uDD10";
    public static final String KEY = "\uD83D\uDD11";
    public static final String IDEA = "\uD83D\uDCA1";
    public static final String GAME = "\uD83C\uDFAE";
    public static final String FINISH = "\uD83C\uDFC1";

    private static final String SOUND_PATH = System.getProperty("user.dir") + "/src/client/sound/";

    /**
     * Internal method that attempts to play sound effect.
     *
     * @param name String, name of the specific sound effect
     */
    private void playSoundEffect(String name) {
        new Thread(() -> {
            try {
                // Opening the handle and stream to our sound effect
                File soundEffect = new File(SOUND_PATH + name);
                AudioInputStream audioStream = AudioSystem.getAudioInputStream(soundEffect);

                Clip clip = (Clip) AudioSystem.getLine(new Line.Info(Clip.class));
                // Creating a listener,
                // that will automatically close open resource after being played
                clip.addLineListener(event -> {
                    if (event.getType().equals(LineEvent.Type.STOP)) {
                        clip.close();
                    }
                });
                clip.open(audioStream);
                clip.start();

            } catch (LineUnavailableException | UnsupportedAudioFileException |
                     IOException ignored) {
            }
        }).start();
    }

    /**
     * Internal method that adds sound effect from incoming messages.
     *
     * @param message String, incoming message
     */
    private void addSoundEffect(String message) {
        if (message.contains(ERROR)) {
            this.playSoundEffect("error.wav");
        } else if (message.contains(INFO)) {
            this.playSoundEffect("info.wav");
        } else if (message.contains(UNKNOWN)) {
            this.playSoundEffect("unknown.wav");
        } else if (message.contains(SUCCESS)) {
            this.playSoundEffect("success.wav");
        } else if (message.contains(IDEA)) {
            this.playSoundEffect("idea.wav");
        } else if (message.contains(GAME)) {
            this.playSoundEffect("game.wav");
        } else if (message.contains(FINISH)) {
            if (message.contains("lost")) {
                this.playSoundEffect("lose.wav");
            } else {
                this.playSoundEffect("winner.wav");
            }
        }
    }

    /**
     * Method that consumes incoming messages
     * that should be delivered to the client and displays it accordingly,
     * supports method chaining.
     *
     * @param message String incoming message
     */
    @Override
    public MessageOperator incomingMessage(String message) {
        this.addSoundEffect(message);
        System.out.println(message);

        return this;
    }
}
